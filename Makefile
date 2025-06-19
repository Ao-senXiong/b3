PROJECT_FILE=src/dfyconfig.toml
TARGET = build/b3
INPUT = "input.b3"

all:
	dafny run $(PROJECT_FILE) --build $(TARGET) -- $(INPUT)

build:
	dafny build $(PROJECT_FILE) --output $(TARGET)

run:
	dafny run --no-verify $(PROJECT_FILE) --build $(TARGET) -- $(INPUT)

verify:
	dafny verify $(PROJECT_FILE)

resolve:
	dafny resolve $(PROJECT_FILE)

test:
	dafny run --no-verify $(PROJECT_FILE) --build $(TARGET) -- $(INPUT) | diff output.expect -
