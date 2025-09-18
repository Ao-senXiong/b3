PROJECT_FILE=src/dfyconfig.toml
TARGET = bin/b3
INPUT = "test/verifier/basics.b3"
EXPECTED_OUTPUT = "input.expect"
JS_TARGET = "bin/b3.js"

all: build lit test-cs

clean:
	rm -rf bin target/cs/bin target/java/bin
	cd doc ; make clean
	cd doc/refman ; make clean

build:
	dafny build $(PROJECT_FILE) --output $(TARGET)

quick:
	dafny build --no-verify $(PROJECT_FILE) --output $(TARGET)

run:
	dafny run --no-verify $(PROJECT_FILE) --build $(TARGET) -- $(INPUT)

verify:
	dafny verify $(PROJECT_FILE)

resolve:
	dafny resolve $(PROJECT_FILE)

# This is the target for running the B3 test suite. (make won't let it be called "test", because there's a directory named "test")
# The --filter option will cause lit to ignore all files (and, in particular, unsupported files) in the "test" folder. This is
# convenient, so that a B3 developer can keep temporary .b3 files in that folder.
lit:
	lit-z3
	lit-cvc5

lit-z3:
	lit --filter '/' test

lit-cvc5:
	lit -D B3_OPTIONS=--cvc5 --filter '/' test/verifier

# C# targets (in addition to the standard targets above)

test-cs:
	(cd target/cs; dafny test --no-verify $(PROJECT_FILE) --output test/b3)

build-cs:
	(cd target/cs; dafny build $(PROJECT_FILE) --output $(TARGET))

# Java targets

build-java:
	(cd target/java; dafny build --target=java $(PROJECT_FILE) --output $(TARGET))

quick-java:
	(cd target/java; dafny build --no-verify --target=java $(PROJECT_FILE) --output $(TARGET))

run-java:
	(cd target/java; dafny run --target=java $(PROJECT_FILE) --no-verify --build $(TARGET) -- verify ../../$(INPUT))

b3-java:
	CLASSPATH=target/java/$(TARGET).jar java b3 verify $(INPUT)

# JavaScript targets

test-js:
	(cd target/js; dafny test --no-verify --target:js src/dfyconfig.toml --output test/b3)

build-js:
	(cd target/js; dafny build --target:js src/dfyconfig.toml --output bin/b3)

translate-js:
	(cd target/js; dafny translate js src/dfyconfig.toml --output bin/b3)

run-js:
	(cd target/js; node bin/b3.js ../../$(INPUT))

# Misc

b3:
	$(TARGET) verify $(INPUT)

docs:
	cd doc ; make
	cd doc/refman ; make
