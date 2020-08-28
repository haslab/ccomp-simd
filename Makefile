all:
	@echo \"make setup_build_dir\" - relinks CCOMP-SIMD files on build dir
	@echo \"make clean_setup_build_dir\" - relinks both COMPCERT and CCOMP-SIMD files

setup_build_dir: scripts/SIMD.files
	@python scripts/setup_build.py ../ccomp-simd build < scripts/SIMD.files

clean_setup_build_dir: scripts/CompCert.files scripts/SIMD.files
	@rm -rf build/*
	@python3 scripts/setup_build.py ../submodules/compcert build < scripts/CompCert.files
	@python3 scripts/setup_build.py ../ccomp-simd build < scripts/SIMD.files

clean:
	@rm -rf build/*
