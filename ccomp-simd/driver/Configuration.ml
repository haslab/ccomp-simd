let stdlib_path = "/usr/local/lib/compcert"
let prepro = "gcc -arch i386 -U__GNUC__ -U__clang__ -U__BLOCKS__ '-D__attribute__(x)=' -E"
let asm = "gcc -arch i386 -c"
let linker = "gcc -arch i386 -Wl,-no_pie"
let arch = "ia32"
let variant = "standard"
let system = "macosx"
let has_runtime_lib = true
let asm_supports_cfi = true
let version = "2.2 (with SIMD support)"
