# JavaScript Build for B3

This directory contains the JavaScript build of the B3 project, including integration with Z3 SMT solver via WebAssembly.

## Running the JavaScript Version

When running the WebAssembly version of Z3 in a browser environment, you may encounter security restrictions due to the browser's same-origin policy. This typically manifests as an error like:

```
Uncaught SecurityError: Failed to construct 'Worker': Script cannot be accessed from origin 'null'.
```

There are two recommended approaches to solve this issue:

## Option 1: Configure Your Browser for Local Development

You can configure your browser to allow local file access, though this is less secure and should only be used for development.

### For Chrome:

1. Close all Chrome instances
2. Create a shortcut to Chrome
3. Right-click the shortcut and select "Properties"
4. In the "Target" field, append: `--allow-file-access-from-files`
   - Example: `"C:\Program Files\Google\Chrome\Application\chrome.exe" --allow-file-access-from-files`
5. Launch Chrome using this shortcut
6. Open your HTML file directly

### For Firefox:

1. Type `about:config` in the address bar
2. Search for `security.fileuri.strict_origin_policy`
3. Set it to `false`
4. Restart Firefox
5. Open your HTML file directly

## Option 2: Use a Local Web Server (Recommended)

The most reliable solution is to serve your files through a local web server instead of opening them directly with `file://` URLs.

### Using Python's built-in server:

```powershell
# Navigate to the js/bin directory
cd target/js/bin

# Start a Python HTTP server
python -m http.server 8000
```

Then access your page at `http://localhost:8000` in your browser.

### Using Node.js http-server:

```powershell
# Install http-server globally if you haven't already
npm install -g http-server

# Navigate to the js/bin directory
cd target/js/bin

# Start the server (with caching disabled)
http-server -c-1
```

Then access your page at the URL shown in the terminal (typically http://localhost:8080).

## Running from Node.js

If you're running the JavaScript build from Node.js rather than a browser, you won't encounter these security restrictions. You can run the compiled JavaScript directly:

```powershell
node bin/b3.js path/to/input.b3
```

## Building the JavaScript Version

To build the JavaScript version of B3:

```powershell
# From the project root
dafny build --target:js target/js/src/dfyconfig.toml --output target/js/bin/b3
```

## Testing

To run tests on the JavaScript build:

```powershell
# From the project root
dafny test --no-verify --target:js target/js/src/dfyconfig.toml --output target/js/test/b3
```

## Project Structure

- `bin/` - Contains the compiled JavaScript output
- `src/` - Contains JavaScript-specific source files
  - `dfyconfig.toml` - Dafny project configuration for JavaScript
  - `Z3Interface.js` - JavaScript implementation of Z3 interface
- `test/` - Contains test output

## Troubleshooting

If you encounter issues with Z3 WebAssembly:

1. Check browser console for specific error messages
2. Ensure you're using a supported browser (Chrome, Firefox, Edge)
3. Verify that all required files are present in the bin directory
4. Try using a different approach from the options above

For Node.js environments, ensure you have the required dependencies installed and that your Node.js version is compatible with the WebAssembly features being used.