LIB_ANTLR := lib/antlr.jar
ANTLR_SCRIPT := Retreet.g4

all: classes

classes:
	mkdir -p build
	java -cp $(LIB_ANTLR) org.antlr.v4.Tool -o build $(ANTLR_SCRIPT)
	mkdir -p classes
	javac -source 1.7 -target 1.7 -cp $(LIB_ANTLR) -d classes src/*.java build/*.java

clean_classes:
	rm -rf classes

clean_parser:
	rm -rf build

clean: clean_classes clean_parser

.PHONY: all classes clean clean_classes clean_parser
