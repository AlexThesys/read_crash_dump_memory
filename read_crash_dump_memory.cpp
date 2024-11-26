#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <windows.h>
#include <dbghelp.h>
#include <psapi.h>
#include <tlhelp32.h>
#include <tchar.h>
#include <assert.h>
#include <emmintrin.h>
#include <omp.h>
#include <mutex>
#include <condition_variable>
#include <vector> // temp

#define MAX_BUFFER_SIZE 0x1000
#define MAX_PATTERN_LEN 0x40
#define MAX_ARG_LEN MAX_PATTERN_LEN
#define MAX_COMMAND_LEN 0X10
#define MAX_OMP_THREADS 8
#define MAX_MEMORY_USAGE_IDEAL 0X40000000
#define TOO_MANY_RESULTS 0x400

#pragma comment(lib, "dbghelp.lib")

enum input_type {
    it_hex,
    it_ascii,
    it_error_type,
};

enum input_command {
    c_help,
    c_search_pattern,
    c_list_memory_regions,
    c_list_memory_regions_info,
    c_list_memory_regions_info_committed,
    c_list_modules,
    c_list_threads,
    c_list_thread_registers,
    c_continue,
    c_quit_program,
};

typedef struct search_data {
    input_type type;
    uint64_t value;
    const char* pattern;
    uint64_t pattern_len;
} search_data;

struct module_data {
    LPWSTR name;
    char* base_of_image;
    uint64_t size_of_image;
};

struct thread_data {
    uint32_t tid;
    uint32_t priority_class;
    uint32_t priority;
    // padding
    //char* teb;
    char* stack_base;
    CONTEXT* context;
};

struct dump_context {
    const char* pattern;
    size_t pattern_len;
    HANDLE file_base;
    std::vector<module_data> m_data;
    std::vector<thread_data> t_data;
};

static const char* page_state[] = { "MEM_COMMIT", "MEM_FREE", "MEM_RESERVE" };
static const char* page_type[] = { "MEM_IMAGE", "MEM_MAPPED", "MEM_PRIVATE" };
static const char* page_protect[] = { "PAGE_EXECUTE", "PAGE_EXECUTE_READ", "PAGE_EXECUTE_READWRITE", "PAGE_EXECUTE_WRITECOPY", "PAGE_NOACCESS", "PAGE_READONLY",
                                    "PAGE_READWRITE", "PAGE_WRITECOPY", "PAGE_TARGETS_INVALID", "UNKNOWN" };

inline int is_hex(const char* pattern, size_t pattern_len) {
    return (((pattern_len > 2) && (pattern[pattern_len - 1] == 'h' || pattern[pattern_len - 1] == 'H'))
        || ((pattern_len > 3) && (pattern[0] == '0' && pattern[1] == 'x')));
}

static const char* get_page_state(DWORD state) {
    const char* result = NULL;
    switch (state) {
    case MEM_COMMIT:
        result = page_state[0];
        break;
    case MEM_FREE:
        result = page_state[1];
        break;
    case MEM_RESERVE:
        result = page_state[2];
        break;
    }
    return result;
}

static void print_page_type(DWORD state) {
    printf("Type:");
    if (state == MEM_IMAGE) {
        printf(" %s\n", page_type[0]);
    }
    else {
        if (state & MEM_MAPPED) {
            printf(" %s ", page_type[1]);
        }
        if (state & MEM_PRIVATE) {
            printf(" %s ", page_type[2]);
        }
        puts("");
    }
}

static bool too_many_results(size_t num_lines) {
    if (num_lines < TOO_MANY_RESULTS) {
        return false;
    }
    printf("Would you like to display %llu results? y/n ", num_lines);
    const char ch = static_cast<char>(getchar());
    while ((getchar()) != '\n'); // flush stdin
    puts("");
    return !(ch == 'y' || ch == 'Y');
}

static const char* get_page_protect(DWORD state) {
    // lets not comlicate things with other available options for now
    state &= ~(PAGE_GUARD | PAGE_NOCACHE | PAGE_WRITECOMBINE);

    const char* result;
    switch (state) {
    case PAGE_EXECUTE:
        result = page_protect[0];
        break;
    case PAGE_EXECUTE_READ:
        result = page_protect[1];
        break;
    case PAGE_EXECUTE_READWRITE:
        result = page_protect[2];
        break;
    case PAGE_EXECUTE_WRITECOPY:
        result = page_protect[3];
        break;
    case PAGE_NOACCESS:
        result = page_protect[4];
        break;
    case PAGE_READONLY:
        result = page_protect[5];
        break;
    case PAGE_READWRITE:
        result = page_protect[6];
        break;
    case PAGE_WRITECOPY:
        result = page_protect[7];
        break;
    case PAGE_TARGETS_INVALID:
        result = page_protect[8];
        break;
    default:
        result = page_protect[9];
        break;
    }
    return result;
}

static bool map_file(const char* dump_file_path, HANDLE* file_handle, HANDLE* file_mapping_handle, LPVOID* file_base) {
    *file_handle = CreateFileA(dump_file_path, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (*file_handle == INVALID_HANDLE_VALUE) {
        perror("Failed to open the file.\n");
        return false;
    }

    *file_mapping_handle = CreateFileMapping(*file_handle, NULL, PAGE_READONLY, 0, 0, NULL);
    if (!*file_mapping_handle) {
        perror("Failed to create file mapping.\n");
        CloseHandle(*file_handle);
        return false;
    }

    *file_base = MapViewOfFile(*file_mapping_handle, FILE_MAP_READ, 0, 0, 0);
    if (!*file_base) {
        perror("Failed to map view of file.\n");
        CloseHandle(*file_mapping_handle);
        CloseHandle(*file_handle);
        return false;
    }

    MINIDUMP_HEADER* header = (MINIDUMP_HEADER*)*file_base;
    
    if (header->Signature != MINIDUMP_SIGNATURE) {
        puts("The provided file is not a crash dump! Exiting...");
        UnmapViewOfFile(*file_base);
        CloseHandle(*file_mapping_handle);
        CloseHandle(*file_handle);
        return false;
    }

    const bool is_full_dump = (header->Flags & MiniDumpWithFullMemory) != 0;
    if (!is_full_dump) {
        puts("Crash dump is not a full dump - no point analysing it. Exiting..");
        UnmapViewOfFile(*file_base);
        CloseHandle(*file_mapping_handle);
        CloseHandle(*file_handle);
        return false;
    }

    return true;
}

static bool list_memory64_regions(const dump_context* ctx) {

    MINIDUMP_MEMORY64_LIST* memory_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, Memory64ListStream, nullptr, reinterpret_cast<void**>(&memory_list), &stream_size)) {
        perror("Failed to read Memory64ListStream.\n");
        return false;
    }

    // Parse and list memory regions
    const ULONG64 num_memory_regions =  memory_list->NumberOfMemoryRanges;
    if (too_many_results(num_memory_regions)) {
        return true;
    }

    printf("*** Number of Memory Regions: %llu ***\n\n", num_memory_regions);

    const MINIDUMP_MEMORY_DESCRIPTOR64* memory_descriptors = (MINIDUMP_MEMORY_DESCRIPTOR64*)((char*)(memory_list) + sizeof(MINIDUMP_MEMORY64_LIST));

    ULONG prev_module = (ULONG)(-1);
    for (ULONG i = 0; i < num_memory_regions; ++i) {
        const MINIDUMP_MEMORY_DESCRIPTOR64& mem_desc = memory_descriptors[i];
        for (size_t m = 0, sz = ctx->m_data.size(); m < sz; m++) {
            const module_data& mdata = ctx->m_data[m];
            if ((prev_module != m) && ((ULONG64)mdata.base_of_image <= mem_desc.StartOfMemoryRange) && (((ULONG64)mdata.base_of_image + mdata.size_of_image) >= mem_desc.StartOfMemoryRange)) {
                puts("------------------------------------\n");
                wprintf((LPWSTR)L"Module name: %s\n", mdata.name);
                prev_module = m;
                break;
            }
        }
        printf("Start Address: 0x%p | Size: 0x%08llx\n", mem_desc.StartOfMemoryRange, mem_desc.DataSize);
    }
    puts("");

    return true;
}

static bool list_memory_regions(const dump_context* ctx) {

    MINIDUMP_MEMORY_LIST* memory_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, MemoryListStream, nullptr, reinterpret_cast<void**>(&memory_list), &stream_size)) {
        perror("Failed to read MemoryListStream.\n");
        return false;
    }

    // Parse and list memory regions
    const ULONG64 num_memory_regions = memory_list->NumberOfMemoryRanges;
    if (too_many_results(num_memory_regions)) {
        return true;
    }

    printf("*** Number of Memory Regions: %llu ***\n\n", num_memory_regions);

    const MINIDUMP_MEMORY_DESCRIPTOR* memory_descriptors = (MINIDUMP_MEMORY_DESCRIPTOR*)((char*)(memory_list)+sizeof(MINIDUMP_MEMORY_LIST));
    
    ULONG prev_module = (ULONG)(-1);
    for (ULONG i = 0; i < num_memory_regions; ++i) {
        const MINIDUMP_MEMORY_DESCRIPTOR& mem_desc = memory_descriptors[i];
        for (size_t m = 0, sz = ctx->m_data.size(); m < sz; m++) {
            const module_data& mdata = ctx->m_data[m];
            if ((prev_module != m) && ((ULONG64)mdata.base_of_image <= mem_desc.StartOfMemoryRange) && (((ULONG64)mdata.base_of_image + mdata.size_of_image) >= mem_desc.StartOfMemoryRange)) {
                puts("------------------------------------\n");
                wprintf((LPWSTR)L"Module name: %s\n", mdata.name);
                prev_module = m;
                break;
            }
        }
        printf("Start Address: 0x%p\n", mem_desc.StartOfMemoryRange);
    }
    puts("");

    return true;
}

static void gather_modules(dump_context *ctx) {
    // Retrieve the Memory64ListStream
    MINIDUMP_MODULE_LIST* module_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, ModuleListStream, nullptr, reinterpret_cast<void**>(&module_list), &stream_size)) {
        perror("Failed to read ModuleListStream.\n");
        return;
    }

    const ULONG64 num_modules = module_list->NumberOfModules;
    const MINIDUMP_MODULE* modules = (MINIDUMP_MODULE*)((char*)(module_list)+sizeof(MINIDUMP_MODULE_LIST));
    ctx->m_data.resize(num_modules);

    for (ULONG i = 0; i < num_modules; i++) {
        const MINIDUMP_MODULE& module = modules[i];
        ctx->m_data[i] = { (WCHAR*)((char*)ctx->file_base + module.ModuleNameRva + sizeof(_MINIDUMP_STRING)), (char*)module.BaseOfImage, module.SizeOfImage };
    }
}

static void gather_threads(dump_context *ctx) {
    MINIDUMP_THREAD_LIST* thread_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, ThreadListStream, nullptr, reinterpret_cast<void**>(&thread_list), &stream_size)) {
        perror("Failed to read ThreadListStream.\n");
        return;
    }

    const ULONG32 num_threads = thread_list->NumberOfThreads;
    const MINIDUMP_THREAD* threads = (MINIDUMP_THREAD*)((char*)(thread_list)+sizeof(MINIDUMP_THREAD_LIST));
    ctx->t_data.resize(num_threads);

    for (ULONG i = 0; i < num_threads; i++) {
        const MINIDUMP_THREAD& thread = threads[i];
        ctx->t_data[i] = { thread.ThreadId, thread.PriorityClass, thread.Priority,/* (char*)thread.Teb,*/ 
                            (char*)(thread.Stack.StartOfMemoryRange+thread.Stack.Memory.DataSize), (CONTEXT*)((char*)ctx->file_base+thread.ThreadContext.Rva)};
    }
}

static void list_modules(const dump_context* ctx) {
    const ULONG64 num_modules = ctx->m_data.size();
    if (too_many_results(num_modules)) {
        return;
    }

    printf("*** Number of Modules: %llu ***\n\n", num_modules);

    for (ULONG i = 0; i < num_modules; i++) {
        const module_data& module = ctx->m_data[i];
        wprintf((LPWSTR)L"Module name: %s\n", module.name);
        printf("Base of image: 0x%p | Size of image: 0x%04llx\n\n", module.base_of_image, module.size_of_image);
    }
}

static void list_threads(const dump_context* ctx) {
    const ULONG64 num_threads = ctx->t_data.size();

    if (too_many_results(num_threads)) {
        return;
    }

    printf("*** Number of threads: %llu ***\n\n", num_threads);

    for (ULONG i = 0; i < num_threads; i++) {
        const thread_data& thread = ctx->t_data[i];
        printf("ThreadID: 0x%04x | Priority Class: 0x%04x | Priority: 0x%04x | Stack Base: 0x%p | RSP: 0x%p\n\n",
            thread.tid, thread.priority_class, thread.priority, (char*)thread.stack_base, (char*)thread.context->Rsp);
    }
}

static void list_thread_registers(const dump_context* ctx) {
    const ULONG64 num_threads = ctx->t_data.size();

    if (too_many_results(num_threads)) {
        return;
    }

    printf("*** Number of threads: %llu ***\n\n", num_threads);

    for (ULONG i = 0; i < num_threads; i++) {
        const thread_data& thread = ctx->t_data[i];
        printf("*** ThreadID: 0x%04x ***\nRAX: 0x%p RBX: 0x%p RCX: 0x%p RDI: 0x%p RSI: 0x%p\n", thread.tid,
            (char*)thread.context->Rax, (char*)thread.context->Rbx, (char*)thread.context->Rcx, (char*)thread.context->Rdx, 
            (char*)thread.context->Rdi, (char*)thread.context->Rsi);
        printf("RSP: 0x%p RBP: 0x%p RIP: 0x%p RFLAGS: 0x%04x MXCSR: 0x%04x\n",
            (char*)thread.context->Rsp, (char*)thread.context->Rbp, (char*)thread.context->Rip,
            (char*)thread.context->EFlags, (char*)thread.context->MxCsr);
        printf("R8:  0x%p R9:  0x%p R10: 0x%p R11: 0x%p\n",
            (char*)thread.context->R8, (char*)thread.context->R9, (char*)thread.context->R10, (char*)thread.context->R11);
        printf("R12: 0x%p R13: 0x%p R14: 0x%p R15: 0x%p\n",
            (char*)thread.context->R11, (char*)thread.context->R12, (char*)thread.context->R13, (char*)thread.context->R14);
        puts("\n----------------\n");
    }
}

static void print_memory_info_list(const dump_context* ctx, bool show_commited) {
    MINIDUMP_MEMORY_INFO_LIST* memory_info_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, MemoryInfoListStream, nullptr, reinterpret_cast<void**>(&memory_info_list), &stream_size)) {
        perror("Failed to read MemoryInfoListStream.\n");
        return;
    }

    const ULONG64 num_entries = memory_info_list->NumberOfEntries;
    if (too_many_results(num_entries)) {
        return;
    }

    if (!show_commited) {
        printf("*** Number of Memory Info Entries: %llu ***\n\n", num_entries);
    }

    const MINIDUMP_MEMORY_INFO* memory_info = (MINIDUMP_MEMORY_INFO*)((char*)(memory_info_list) + sizeof(MINIDUMP_MEMORY_INFO_LIST));

    ULONG prev_module = (ULONG)(-1);
    for (ULONG i = 0; i < memory_info_list->NumberOfEntries; ++i) {
        const MINIDUMP_MEMORY_INFO& mem_info = memory_info[i];
        if (show_commited && (mem_info.State != MEM_COMMIT)) {
            continue;
        }
        for (size_t m = 0, sz = ctx->m_data.size(); m < sz; m++) {
            const module_data& mdata = ctx->m_data[m];
            if ((prev_module != m) && ((ULONG64)mdata.base_of_image <= mem_info.BaseAddress) && (((ULONG64)mdata.base_of_image + mdata.size_of_image) >= mem_info.BaseAddress)) {
                puts("------------------------------------\n");
                wprintf((LPWSTR)L"Module name: %s\n", mdata.name);
                prev_module = m;
                break;
            }
        }
        printf("Base Address: 0x%p | Size: 0x%08llx | State: %s\t | Protect: %s\t",
            memory_info[i].BaseAddress, memory_info[i].RegionSize, 
            get_page_state(mem_info.State), get_page_protect(mem_info.Protect));
        print_page_type(mem_info.Type);
    }
    puts("");
}

#define _max(x,y) (x) > (y) ? (x) : (y)
#define _min(x,y) (x) < (y) ? (x) : (y)
#define step (sizeof(__m128i) / sizeof(uint8_t))

static const uint8_t* strstr_u8(const uint8_t* str, size_t str_sz, const uint8_t* substr, size_t substr_sz) {
    if (/*!substr_sz || */(str_sz < substr_sz))
        return NULL;

    const __m128i first = _mm_set1_epi8(substr[0]);
    const __m128i last = _mm_set1_epi8(substr[substr_sz - 1]);
    const uint8_t skip_first = (uint8_t)(substr_sz > 2);
    const size_t cmp_size = substr_sz - (1llu << skip_first);

    for (size_t j = 0, sz = str_sz - substr_sz; j <= sz; j += step) {
        const uint8_t* f = str + j;
        const uint8_t* l = str + j + substr_sz - 1;
        __m128i xmm0 = _mm_loadu_si128(reinterpret_cast<const __m128i*>(f));
        __m128i xmm1 = _mm_loadu_si128(reinterpret_cast<const __m128i*>(l));

        xmm0 = _mm_cmpeq_epi8(first, xmm0);
        xmm1 = _mm_cmpeq_epi8(last, xmm1);
        xmm0 = _mm_and_si128(xmm0, xmm1);

        uint32_t mask = (uint32_t)_mm_movemask_epi8(xmm0);

        const uint8_t max_offset = (uint8_t)_min(step, str_sz - (j + substr_sz) + 1);
        const uint32_t max_offset_mask = (1 << max_offset) - 1;
        mask &= max_offset_mask;
        unsigned long bit = 0;

        while (_BitScanForward(&bit, mask)) {
            const uint32_t offset = bit;
            const uint8_t* m0 = str + j + offset + skip_first;
            const uint8_t* m1 = substr + skip_first;
            if (memcmp(m0, m1, cmp_size) == 0)
                return (str + j + offset);

            mask ^= (1 << bit); // clear bit
        }
    }

    return NULL;
}

static std::mutex g_mtx;
static std::condition_variable g_cv;
static LONG g_memory_usage_bytes = 0; // accessed from different threads
static int g_max_omp_threads = MAX_OMP_THREADS;

static void find_pattern(const dump_context *ctx, const MINIDUMP_MEMORY_DESCRIPTOR64* memory_descriptors, const MINIDUMP_MEMORY64_LIST* memory_list) {
    std::vector<std::vector<const char*>> match;
    std::vector<const char*> p;
    std::vector<MINIDUMP_MEMORY_DESCRIPTOR64> info;
    size_t max_memory_usage = MAX_MEMORY_USAGE_IDEAL;

    puts("Searching crash dump memory...");
    puts("\n------------------------------------\n");
    {
        size_t cumulative_offset = 0;
        for (ULONG i = 0, sz = memory_list->NumberOfMemoryRanges; i < sz; ++i) {
            const MINIDUMP_MEMORY_DESCRIPTOR64& mem_desc = memory_descriptors[i];
            char* memory_data = reinterpret_cast<char*>(ctx->file_base) + memory_list->BaseRva + cumulative_offset;
            SIZE_T memory_size = static_cast<SIZE_T>(mem_desc.DataSize);
            info.push_back(mem_desc);
            p.push_back(memory_data);
            max_memory_usage = _max(max_memory_usage, mem_desc.DataSize);
            cumulative_offset += mem_desc.DataSize;
        }
    }
    const size_t num_regions = info.size();
    match.resize(num_regions);

    const char* pattern = ctx->pattern;
    const size_t pattern_len = ctx->pattern_len;

    const int num_threads = _min(g_max_omp_threads, omp_get_num_procs());
    omp_set_num_threads(num_threads);   
#pragma omp parallel for schedule(dynamic, 1) shared(match,p,info)
    for (int64_t i = 0;  i < (int64_t)num_regions; i++) {
        size_t region_size = info[i].DataSize;
        {
            std::unique_lock<std::mutex> lk(g_mtx);
            while (true) {
                g_cv.wait(lk, [max_memory_usage] { return (g_memory_usage_bytes < max_memory_usage); });
                if (g_memory_usage_bytes < max_memory_usage) {
                    g_memory_usage_bytes += region_size;
                    break;
                }
            }
        }

        const char* buffer = p[i];
        if (!buffer) {
            puts("Empty memory region!");
            continue;
        }

        if (region_size >= pattern_len) {
            const char* buffer_ptr = buffer;
            size_t buffer_size = region_size;

            while (buffer_size >= pattern_len) {
                const char* old_buf_ptr = buffer_ptr;
                buffer_ptr = (const char*)strstr_u8((const uint8_t*)buffer_ptr, buffer_size, (const uint8_t*)pattern, pattern_len);
                if (!buffer_ptr) {
                    break;
                }

                const size_t buffer_offset = buffer_ptr - buffer;
                match[i].push_back((const char*)(info[i].StartOfMemoryRange + buffer_offset));

                buffer_ptr++;
                buffer_size -= (buffer_ptr - old_buf_ptr);
            }
        }
        {
            std::unique_lock<std::mutex> lk(g_mtx);
            g_memory_usage_bytes -= region_size;
        }
        g_cv.notify_all(); // permitted to be called concurrentely
    }

    size_t num_matches = 0;
    for (const auto& m : match) {
        num_matches += m.size();
    }
    if (!num_matches) {
        puts("*** No matches found. ***");
        return;
    }
    if (too_many_results(num_matches)) {
        return;
    }
    printf("*** Total number of matches: %llu ***\n\n", num_matches);
    
    //size_t prev_module = (size_t)(-1);
    for (size_t i = 0; i < num_regions; i++) {
        if (match[i].size()) {
            for (size_t m = 0, sz = ctx->m_data.size(); m < sz; m++) {
                const module_data& mdata = ctx->m_data[m];
                if (/*(prev_module != m) && */((ULONG64)mdata.base_of_image <= info[i].StartOfMemoryRange) && (((ULONG64)mdata.base_of_image + mdata.size_of_image) >= info[i].StartOfMemoryRange)) {
                    puts("------------------------------------\n");
                    wprintf((LPWSTR)L"Module name: %s\n", mdata.name);
                    /*prev_module = m;*/
                    break;
                }
            }
            //for (size_t t = 0, sz = ctx->t_data.size(); t < sz; t++) {
            //    const thread_data& tdata = ctx->t_data[t];
            //    if (((ULONG64)tdata.stack_base >= info[i].StartOfMemoryRange) && (tdata.context->Rsp <= info[i].StartOfMemoryRange)) {
            //        puts("------------------------------------\n");
            //        wprintf((LPWSTR)L"Stack: Thread Id 0x%04x\n", tdata.tid);
            //        break;
            //    }
            //}

            printf("Start of Memory Region: 0x%p | Region Size: 0x%08llx\n\n",
                info[i].StartOfMemoryRange, info[i].DataSize);
            for (const char* m : match[i]) {
                printf("\tMatch at address: 0x%p\n", m);
            }
            puts("");
        }
    }
}

static void search_pattern_in_dump(const dump_context *ctx) {
    MINIDUMP_MEMORY64_LIST* memory_list = nullptr;
    ULONG stream_size = 0;
    if (!MiniDumpReadDumpStream(ctx->file_base, Memory64ListStream, nullptr, reinterpret_cast<void**>(&memory_list), &stream_size)) {
        perror("Failed to read Memory64ListStream.\n");
        return;
    }

    const MINIDUMP_MEMORY_DESCRIPTOR64* memory_descriptors = (MINIDUMP_MEMORY_DESCRIPTOR64*)((char*)(memory_list)+sizeof(MINIDUMP_MEMORY64_LIST));
    find_pattern(ctx, memory_descriptors, memory_list);

}

static const char* unknown_command = "Unknown command.";

static void parse_input(const char* pattern, search_data *data) {
    if (data->pattern_len > MAX_PATTERN_LEN) {
        fprintf(stderr, "Pattern exceeded maximum size of %d. Exiting...", MAX_PATTERN_LEN);
        data->type = it_error_type;
        return;
    }
    uint64_t value = 0;
    char* end;
    value = strtoull(pattern, &end, 0x10);
    const int is_hex = (pattern != end);

    if (is_hex) {
        data->type = it_hex;
        data->value = value;
        data->pattern = (const char*)&data->value;
        if (*end == 'h' || *end == 'H') {
            data->pattern_len = size_t(end - pattern);
        } else if (pattern[0] == '0' && (pattern[1] == 'x' || pattern[1] == 'X')) {
            data->pattern_len -= 1;
        }
        data->pattern_len /= 2;
        if (data->pattern_len <= sizeof(uint64_t)) {
            puts("\nSearching for a hex value...\n");
        } else {
            printf("Max supported hex value size: %d bytes!\n", (int)sizeof(uint64_t));
            data->type = it_error_type;
        }
    } else {
        data->type = it_ascii;
        data->pattern = pattern;
        puts("\nSearching for an ascii string...\n");
    }
}

static constexpr int check_architecture_ct() {
#if defined(__x86_64__) || defined(_M_X64)
    return 1;
#elif defined(i386) || defined(__i386__) || defined(__i386) || defined(_M_IX86)
    return 1;
#else
    return 0;
#endif
}
static_assert(check_architecture_ct(), "Only x86-64 architecture is supported at the moment!");

static int check_architecture_rt() {
    SYSTEM_INFO SystemInfo;
    GetSystemInfo(&SystemInfo);
    return int(SystemInfo.wProcessorArchitecture == PROCESSOR_ARCHITECTURE_AMD64
                || SystemInfo.wProcessorArchitecture == PROCESSOR_ARCHITECTURE_INTEL);
}

static const char* cmd_args[] = { "-h", "--help", "-t=", "--threads=", "-v", "--version" };
static constexpr size_t cmd_args_size = _countof(cmd_args) / 2; // given that every option has a long and a short forms
static const char* program_version = "version 0.1.0";

static bool parse_cmd_args(int argc, const char** argv) {
    if (argc > (cmd_args_size + 1)) {
        puts("\nToo many arguments provided: some will be discarded.");
    }

    for (int i = 1, sz = _min((int)cmd_args_size, argc); i < sz; i++) {
        if ((0 == strcmp(argv[i], cmd_args[0])) || (0 == strcmp(argv[i], cmd_args[1]))) { // help
            puts("\n-t=<num_threads> || --threads=\t\t -- limits the number of OMP threads");
            return false;
        } else if ((argv[i] == strstr(argv[i], cmd_args[4])) || (argv[i] == strstr(argv[i], cmd_args[5]))) { // OMP threads
            const char* num_t = (argv[i][1] == '-') ? (argv[i] + strlen(cmd_args[5])) : (argv[i] + strlen(cmd_args[4]));
            char* end = NULL;
            size_t arg_len = strlen(num_t);
            DWORD num_threads = strtoul(num_t, &end, is_hex(num_t, arg_len) ? 16 : 10);
            if (num_t != end) {
                num_threads = _max(1, num_threads);
                g_max_omp_threads = _min(num_threads, g_max_omp_threads);
            }
        } else if ((0 == strcmp(argv[i], cmd_args[6])) || (0 == strcmp(argv[i], cmd_args[7]))) { // version
            puts(program_version);
            return false;
        }
        // ...
    }
    return true;
}

void print_help() {
    puts("********************************");
    puts("?\t\t\t - list commands (this message)");
    puts("/ <pattern>\t\t - search for hex value or ascii string (no whitespace)");
    puts("q\t\t\t - quit the program");
    puts("lmr\t\t\t - list memory regions");
    puts("lmi\t\t\t - list memory regions info");
    puts("lmic\t\t\t - list committed memory regions info");
    puts("lM\t\t\t - list process modules");
    puts("lt\t\t\t - list process threads");
    puts("lr\t\t\t - list thread registers");
    puts("********************************\n");
}

char* skip_to_args(char *cmd, size_t len) {
    bool found = false;
    size_t cur_len = 0;
    // skip whitespace
    while (((cur_len < len) && (cmd[cur_len] != 0))) {
        if (!isspace(cmd[cur_len])) {
            break;
        }
        cur_len++;
    }
    // skip to whitespace
    while (((cur_len < len) && (cmd[cur_len] != 0))) {
        if (isspace(cmd[cur_len])) {
            break;
        }
        cur_len++;
    }
    // skip whitespace
    while (((cur_len < len) && (cmd[cur_len] != 0))) {
        if (!isspace(cmd[cur_len])) {
            found = true;
            break;
        }
        cur_len++;
    }
    return found ? (cmd + cur_len) : nullptr;
}

input_command parse_command(dump_context *ctx, search_data *data, char *pattern) {
    input_command command;
    char cmd[MAX_COMMAND_LEN+MAX_ARG_LEN];
    memset(cmd, 0, sizeof(cmd));
    const char *res = gets_s(cmd, sizeof(cmd));
    if (res == nullptr) {
        puts("Empty input.");
        return c_continue;
    }
    if ((cmd[0] == 'q') || (cmd[0] == 'Q')) {
        puts("\n==== Exiting... ====");
        command = c_quit_program;
    } else if (cmd[0] == '?') {
        command = c_help;
    } else if (cmd[0] == '/') {
        memset(pattern, 0, MAX_PATTERN_LEN);
        size_t pattern_len = strlen(cmd);
        char* args = skip_to_args(cmd, pattern_len);
        if (args == nullptr) {
            puts("Pattern missing.");
            return c_continue;
        }
        pattern_len -= (ptrdiff_t)(args - cmd);
        memcpy(pattern, args, pattern_len);
        data->pattern_len = pattern_len;

        parse_input(pattern, data);
        if (data->type == it_error_type) {
            puts("Error parsing the pattern.");
            command = c_continue;
        } else {
            ctx->pattern = data->pattern;
            ctx->pattern_len = data->pattern_len;
            command = c_search_pattern;
        }
    } else if (cmd[0] == 'l') {
        if (cmd[1] == 'M') {
            command = c_list_modules;
        } else if (cmd[1] == 't') {
            if (cmd[2] == 0) {
                command = c_list_threads;
            } else if (cmd[2] =='r') {
                command = c_list_thread_registers;
            } else {
                puts(unknown_command);
                command = c_continue;
            }
        } else if (cmd[1] == 'm') {
            if (cmd[2] == 'r') {
                command = c_list_memory_regions;
            } else if (cmd[2] == 'i') {
                if (cmd[3] == 0) {
                    command = c_list_memory_regions_info;
                } else if (cmd[3] == 'c') {
                    command = c_list_memory_regions_info_committed;
                } else {
                    puts(unknown_command);
                    command = c_continue;
                }
            } else {
                puts(unknown_command);
                command = c_continue;
            }
        } else {
            puts(unknown_command);
            command = c_continue;
        }
    } else {
        puts(unknown_command);
        command = c_continue;
    }
    puts("");

    return command;
}

void execute_command(input_command cmd, const dump_context *ctx) {
    switch (cmd) {
    case c_help :
        print_help();
        break;
    case c_search_pattern : {
        search_pattern_in_dump(ctx);
        break;
    }
    case c_list_memory_regions :
        if (!list_memory64_regions(ctx)) {
            list_memory_regions(ctx);
        }
        break;
    case c_list_memory_regions_info :
        print_memory_info_list(ctx, false);
        break;
    case c_list_memory_regions_info_committed:
        print_memory_info_list(ctx, true);
        break;
    case c_list_modules:
        list_modules(ctx);
        break;
    case c_list_threads:
        list_threads(ctx);
        break;
    case c_list_thread_registers:
        list_thread_registers(ctx);
        break;
    default :
        puts(unknown_command);
        break;
    }
    puts("====================================\n");
}

int main(int argc, const char** argv) {
    if (!check_architecture_rt()) {
        puts("\nOnly x86-64 architecture is supported at the moment!");
        return 1;
    }

    if (!parse_cmd_args(argc, argv)) {
        return 0;
    }

    char dump_file_path[MAX_PATH];
    memset(dump_file_path, 0, sizeof(dump_file_path));
    printf("\nProvide the path to the dmp file: ");
    gets_s(dump_file_path, sizeof(dump_file_path));
    puts("");

    HANDLE file_handle, file_mapping_handle, file_base;
    if (!map_file(dump_file_path, &file_handle, &file_mapping_handle, &file_base)) {
        return -1;
    }

    dump_context ctx = { nullptr, 0, file_base };
    gather_modules(&ctx);
    gather_threads(&ctx);

    char pattern[MAX_PATTERN_LEN];
    search_data data;

    print_help();
    while (1) {
        printf(">: ");
        input_command cmd = parse_command(&ctx, &data, pattern);
        if (cmd == c_quit_program) {
            break;
        } else if (cmd == c_continue) {
            continue;
        }
        execute_command(cmd, &ctx);
    }

    // epilogue
    UnmapViewOfFile(file_base);
    CloseHandle(file_mapping_handle);
    CloseHandle(file_handle);

    return 0;
}
