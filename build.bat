@echo off

set PATH=C:\Program Files (x86)\CMake\bin\;C:\Users\Vlad\AppData\Roaming\local\bin\;C:\usr\ghc8\bin\;C:\usr\ghc8\mingw\bin\;C:\Windows\System32\
set PATH=%PATH%;C:\MinGW\msys\1.0\bin\

agda --ghc app/test.agda --compile-dir ../.agda-ghc
rem agda --js app/test-js.agda --compile-dir ../.agda-js
