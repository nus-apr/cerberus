# Fix build script of Prophet
sed -i '79d' /prophet-gpl/tools/gmp-build.py
sed -i '79i \\tret = subprocess.call(["make", "CFLAGS=\\"-static\\""], env = my_env);'  /prophet-gpl/tools/gmp-build.py

