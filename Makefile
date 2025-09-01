PROJECT_FILE=src/dfyconfig.toml
TARGET = "bin/b3"
INPUT = "input.b3"
EXPECTED_OUTPUT = "input.expect"
JS_TARGET = "bin/b3.js"

all: build lit

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

lit:
	lit test

test-cs:
	(cd target/cs; dafny test --no-verify $(PROJECT_FILE) --output test/b3)

build-cs:
	(cd target/cs; dafny build $(PROJECT_FILE) --output bin/b3)

# JavaScript targets
test-js:
	(cd target/js; dafny test --no-verify --target:js src/dfyconfig.toml --output test/b3)

build-js:
	(cd target/js; dafny build --target:js src/dfyconfig.toml --output bin/b3)

translate-js:
	(cd target/js; dafny translate js src/dfyconfig.toml --output bin/b3)

run-js:
	(cd target/js; node bin/b3.js ../../$(INPUT))

b3:
	$(TARGET) verify $(INPUT)

docs:
	cd doc ; make
