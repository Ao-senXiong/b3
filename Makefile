PROJECT_FILE=src/dfyconfig.toml
TARGET = build/b3

all:
	dafny run $(PROJECT_FILE) --build $(TARGET)

build:
	dafny build $(PROJECT_FILE) --output $(TARGET)

run:
	dafny run --no-verify $(PROJECT_FILE) --build $(TARGET)

verify:
	dafny verify $(PROJECT_FILE)
