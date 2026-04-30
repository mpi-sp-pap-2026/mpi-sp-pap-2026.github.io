@echo off
setlocal enabledelayedexpansion

REM ============================================================
REM  build_sf.bat - Compile all *.v files in dependency order
REM  Uses coqdep -sort to mimic what coq_makefile does.
REM
REM  Usage: build_sf.bat        (compile all)
REM         build_sf.bat clean  (remove generated files)
REM ============================================================

if not exist Makefile (
    echo [ERROR] Makefile not found. Run inside an SF volume folder.
    exit /b 1
)

REM ---------- Clean target ----------
if /i "%~1"=="clean" (
    echo Cleaning compiled files...
    del /q *.vo *.vos *.vok *.glob *.aux *.v.d 2>nul
    del /q .*.aux .lia.cache .nia.cache 2>nul
    del /q Makefile.coq Makefile.coq.conf 2>nul
    echo Done.
    exit /b 0
)

REM ---------- Extract COQMFFLAGS from Makefile ----------
set "QFLAG="
for /f "usebackq tokens=1,* delims==" %%a in ("Makefile") do (
    set "KEY=%%a"
    set "KEY=!KEY: =!"
    if "!KEY!"=="COQMFFLAGS:" set "QFLAG=%%b"
    if "!KEY!"=="COQMFFLAGS"  set "QFLAG=%%b"
)
if defined QFLAG (
    for /f "tokens=*" %%x in ("!QFLAG!") do set "QFLAG=%%x"
)
if "!QFLAG!"=="" (
    echo [ERROR] Could not read COQMFFLAGS from Makefile.
    exit /b 1
)

echo ============================================================
echo  Rocq options: !QFLAG!
echo ============================================================

REM ---------- Compute compile order with coqdep -sort ----------
echo Computing dependency order...
set "VFILES="
for /f "delims=" %%L in ('rocq dep -sort !QFLAG! *.v 2^>nul') do (
    set "VFILES=!VFILES! %%L"
)

REM Fallback to legacy coqdep if `rocq dep` is unavailable
if "!VFILES!"=="" (
    for /f "delims=" %%L in ('coqdep -sort !QFLAG! *.v 2^>nul') do (
        set "VFILES=!VFILES! %%L"
    )
)

if "!VFILES!"=="" (
    echo [ERROR] Failed to compute dependency order.
    echo         Make sure `rocq dep` or `coqdep` is on your PATH.
    exit /b 1
)

echo Order: !VFILES!
echo.

REM ---------- Compile in order ----------
set "COUNT=0"
set "FAIL=0"
for %%f in (!VFILES!) do (
    set /a COUNT+=1
    echo [!COUNT!] Compiling: %%f
    rocq compile !QFLAG! %%f
    if !errorlevel! neq 0 (
        echo.
        echo [FAIL] Failed to compile %%f
        set /a FAIL+=1
        goto :done
    )
    echo       [OK]
    echo.
)

:done
echo ============================================================
if !FAIL! equ 0 (
    echo  All !COUNT! files compiled successfully!
) else (
    echo  Compilation stopped at file !COUNT! due to error.
)
echo ============================================================

endlocal