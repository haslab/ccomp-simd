all:
	@echo \"make download\" - downloads CompCert v2.3pl2
	@echo \"make clean_setup_build_dir\" - relinks both COMPCERT and CCOMP-SIMD files
	@echo \"make setup_build_dir\" - relinks CCOMP-SIMD files on build dir

download:
	@wget https://github.com/AbsInt/CompCert/archive/v2.3pl2.tar.gz
	@tar xvzf v2.3pl2.tar.gz

setup_build_dir: scripts/SIMD.files
	@python scripts/setup_build.py ../ccomp-simd build < scripts/SIMD.files

clean_setup_build_dir: scripts/CompCert.files scripts/SIMD.files
	@rm -rf build/*
	@cp compcert-2.3pl2/.depend build/
	@python3 scripts/setup_build.py ../compcert-2.3pl2 build < scripts/CompCert.files
	@python3 scripts/setup_build.py ../ccomp-simd build < scripts/SIMD.files

clean:
	@rm -rf build/*
