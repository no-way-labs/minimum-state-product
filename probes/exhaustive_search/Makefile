CC     ?= cc
CFLAGS ?= -O3 -std=c11 -Wall -Wextra

exhaustive: exhaustive.c
	$(CC) $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	rm -f exhaustive
