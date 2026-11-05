# The two C programs: the classical computation and the computation of IUT in the reading of IUT IV.  make
CC = gcc
CFLAGS ?= -O2 -Wall -Wextra -std=c11

all: classical iut

classical: classical.c localdata.h
	$(CC) $(CFLAGS) -o $@ classical.c -lm

iut: iut.c localdata.h
	$(CC) $(CFLAGS) -o $@ iut.c -lm

clean:
	rm -f classical iut
