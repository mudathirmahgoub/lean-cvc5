clear
rm -rf .lake/build/lib
lake build
lake build main_executable
.lake/build/bin/main_executable
