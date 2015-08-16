SRCS = Interpreter.oz Gui.oz Parser.oz Lexer.oz Utils.oz Main.oz
OBJS = $(SRCS:.oz=.ozf)
MAIN = Main.oz
EXECUTABLE = Main

.PHONY: clean

$(EXECUTABLE): $(OBJS) $(MAIN)

Parser.ozf: Parser.oz
	ozc -c Parser.oz -o Parser.ozf

Lexer.ozf: Lexer.oz
	ozc -c Lexer.oz -o Lexer.ozf

Gui.ozf: Gui.oz
	ozc -c Gui.oz -o Gui.ozf

Utils.ozf: Utils.oz
	ozc -c Utils.oz -o Utils.ozf

Interpreter.ozf: Interpreter.oz
	ozc -c Interpreter.oz -o Interpreter.ozf

Main.ozf: Main.oz Parser.ozf Lexer.ozf Interpreter.ozf Gui.ozf Utils.ozf
	ozc -c Main.oz -o Main.ozf

all: $(EXECUTABLE)

clean:
	rm -f $(OBJS)
