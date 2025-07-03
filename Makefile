PROJECT_FILE=src/dfyconfig.toml
TARGET = "bin/b3"
INPUT = "input.b3"
EXPECTED_OUTPUT = "input.expect"

all: build test

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

test:
	$(TARGET) $(INPUT) | diff $(EXPECTED_OUTPUT) -

b3:
	$(TARGET) $(INPUT)

docs:
	cd doc ; make
