// B3 Compiler Browser Wrapper
(function () {
  // Save references to browser globals
  var originalConsole = {
    log: console.log,
    error: console.error
  };

  // Create a global _dafny object if it doesn't exist
  if (typeof window._dafny === 'undefined') {
    // Mock the Dafny runtime
    window._dafny = {
      Seq: {
        of: function () {
          var args = Array.prototype.slice.call(arguments);
          return args;
        },
        UnicodeFromString: function (str) {
          return str;
        },
        from: function (arr, mapFn) {
          if (typeof mapFn === 'function') {
            return Array.prototype.map.call(arr, mapFn);
          }
          return Array.from(arr);
        }
      },
      HandleHaltExceptions: function (fn) {
        try {
          return fn();
        } catch (e) {
          console.error("Halted with exception:", e);
        }
      },
      UnicodeFromMainArguments: function (args) {
        // Convert string arguments to Dafny sequences
        return args.map(function (arg) {
          return _dafny.Seq.UnicodeFromString(arg);
        });
      },
      toString: function (obj) {
        return String(obj);
      },
      ZERO: 0,
      ONE: 1,
      BitwiseAnd: function (a, b) { return a & b; },
      BitwiseOr: function (a, b) { return a | b; },
      ShiftLeft: function (a, b) { return a << b; },
      ShiftRight: function (a, b) { return a >> b; },
      EuclideanDivision: function (a, b) { return Math.floor(a / b); }
    };
  }

  // Create a virtual file system
  var virtualFS = {
    files: {},

    writeFile: function (path, data, options) {
      // Store the data in the format expected by the file system
      this.files[path] = data;
    },

    readFile: function (path, options) {
      if (this.files[path] !== undefined) {
        var content = this.files[path];

        // Handle different encoding options
        if (options) {
          if (options.encoding === 'utf8' || options.encoding === 'utf-8') {
            return content;
          } else if (options.encoding === null) {
            // Return as Buffer-like object
            var buf = new Uint8Array(content.length);
            for (var i = 0; i < content.length; i++) {
              buf[i] = content.charCodeAt(i);
            }
            return buf;
          }
        }

        return content;
      }
      throw new Error("File not found: " + path);
    },

    existsSync: function (path) {
      return this.files[path] !== undefined;
    }
  };

  // Create global process object
  window.process = {
    argv: ['node', 'b3.js'],
    stdout: {
      write: function (text) {
        if (window.B3Runner && window.B3Runner.print) {
          window.B3Runner.print(text);
        } else {
          originalConsole.log(text);
        }
      }
    },
    stderr: {
      write: function (text) {
        if (window.B3Runner && window.B3Runner.printErr) {
          window.B3Runner.printErr(text);
        } else {
          originalConsole.error(text);
        }
      }
    }
  };

  // Mock Node.js modules
  var mockModules = {
    fs: {
      readFileSync: function (path, options) {
        try {
          return virtualFS.readFile(path, options);
        } catch (e) {
          throw new Error("Error reading file: " + path + " - " + e.message);
        }
      },
      writeFileSync: function (path, data, options) {
        try {
          virtualFS.writeFile(path, data, options);
        } catch (e) {
          throw new Error("Error writing file: " + path + " - " + e.message);
        }
      },
      existsSync: function (path) {
        return virtualFS.existsSync(path);
      }
    },
    path: {
      join: function () {
        return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/');
      },
      dirname: function (path) {
        return path.replace(/\/[^\/]*$/, '');
      },
      basename: function (path) {
        return path.replace(/^.*\//, '');
      }
    },
    buffer: {
      Buffer: {
        from: function (data, encoding) {
          if (typeof data === 'string') {
            var buf = new Uint8Array(data.length);
            for (var i = 0; i < data.length; i++) {
              buf[i] = data.charCodeAt(i);
            }
            return buf;
          }
          return data;
        },
        isBuffer: function (obj) {
          return obj instanceof Uint8Array;
        }
      }
    },
    process: window.process
  };

  // Mock require function
  window.require = function (moduleName) {
    if (moduleName === 'bignumber.js') {
      // Return the global BigNumber constructor
      return window.BigNumber;
    }
    if (moduleName === 'process') {
      // Return a process object with argv as a proper sequence
      return {
        argv: []
      };
    }
    if (mockModules[moduleName]) {
      return mockModules[moduleName];
    }
    throw new Error("Module not found: " + moduleName);
  };

  // Ensure BigNumber is properly configured for Dafny
  if (typeof window.BigNumber !== 'undefined') {
    // Configure BigNumber for Dafny's needs
    BigNumber.config({
      DECIMAL_PLACES: 20,
      ROUNDING_MODE: BigNumber.ROUND_HALF_EVEN,
      EXPONENTIAL_AT: [-1000000, 1000000]
    });
  } else {
    console.error("BigNumber.js library not loaded!");
  }

  // Create B3Runner to handle the B3 execution
  window.B3Runner = {
    init: function (options) {
      this.options = options || {};
      this.print = options.print || originalConsole.log;
      this.printErr = options.printErr || originalConsole.error;

      // Update process.argv with the input file
      mockModules.process.argv = ['node', 'b3.js'];

      // Set up stdout/stderr redirection
      console.log = function () {
        var args = Array.prototype.slice.call(arguments);
        var message = args.join(' ');
        if (window.B3Runner.print) {
          window.B3Runner.print(message);
        }
      };

      console.error = function () {
        var args = Array.prototype.slice.call(arguments);
        var message = args.join(' ');
        if (window.B3Runner.printErr) {
          window.B3Runner.printErr(message);
        }
      };

      if (options.onRuntimeInitialized) {
        setTimeout(options.onRuntimeInitialized, 100);
      }
    },

    run: function (inputFile, inputContent) {
      try {
        // Store the current input file
        this.currentInputFile = inputFile;

        // Write the input file to the virtual filesystem
        virtualFS.writeFile(inputFile, String(inputContent));

        // Set up the process.argv array with the correct arguments
        var programArgs = ['b3.js', inputFile];

        // Update the global process.argv
        window.process.argv = programArgs;
        mockModules.process.argv = programArgs;

        // Run the B3 compiler
        if (typeof B3 !== 'undefined' && B3.__default) {
          this.print("Running B3 compiler on " + inputFile);

          // Create a proper Dafny sequence for the arguments
          // Looking at the B3.__default.Main function, it expects a sequence of strings
          // with a length property of 2

          // First, let's try a direct approach by creating a custom sequence object
          var dafnyArgs = {
            length: 2,
            "0": _dafny.Seq.UnicodeFromString('b3.js'),
            "1": _dafny.Seq.UnicodeFromString(inputFile),
            isEqualTo: function () { return false; }, // Mock comparison method
            toString: function () { return "Seq#2" }
          };

          // Call the Main function with the arguments
          B3.__default.Main(dafnyArgs);

          return true;
        } else {
          this.printErr("B3 compiler not loaded properly");
          return false;
        }
      } catch (e) {
        this.printErr("Error running B3 compiler: " + e.message);
        return false;
      } finally {
        // Reset process.argv but keep currentInputFile
        window.process.argv = ['b3.js'];
        mockModules.process.argv = ['b3.js'];
      }
    },

    // Expose the virtual filesystem
    FS: virtualFS
  };
})();