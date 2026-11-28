@echo off
rem Run the AxiomWeave CLI without typing "uv run" (Windows).
rem Usage: axw.bat check examples\logic\implication.py
rem Works from any directory; relative paths are resolved from the current directory.
setlocal

where uv >nul 2>nul
if errorlevel 1 goto :no_uv

rem "%~dp0." avoids a trailing backslash escaping the closing quote.
uv run --quiet --project "%~dp0." axw %*
exit /b %ERRORLEVEL%

:no_uv
echo axw: uv is not installed or not on PATH. See https://docs.astral.sh/uv/ 1>&2
exit /b 1
