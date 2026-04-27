# Optional JDK shim (WSL / exotic setups)

Isabelle ships its own JVM under `contrib/jdk-*`; you normally do **not** need this directory.

Use a shim only when you must point **`java`** at a specific binary (e.g. WSL invoking the Windows JDK bundled with a Windows Isabelle install).

1. Copy the example script and put it on your **`PATH`** ahead of system Java, **or** name it `jdk-shim/bin/java` and prepend that directory to `PATH`:

   ```bash
   cp java.wsl-example.sh /path/on/your/PATH/java
   chmod +x /path/on/your/PATH/java
   ```

2. Edit the script: set `JAVA_EXE` to **your** Isabelle contrib JDK `java` / `java.exe`.

Do **not** commit a personalised `java` shim into git (paths are machine-specific).
