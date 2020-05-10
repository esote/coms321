PROG=	emu
SRCS=	emu.c

CFLAGS=		-O2 -fstack-protector -D_FORTIFY_SOURCE=2 -pie -fPIE
LDFLAGS=	-Wl,-z,now -Wl,-z,relro
DEBUGFLAGS=	-std=c99 -pedantic -g -Wall -Wextra -Wconversion

$(PROG): $(SRCS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(PROG).out $(SRCS)

debug: $(SRCS)
	$(CC) $(DEBUGFLAGS) -o $(PROG).out $(SRCS)

clean:
	rm -f $(PROG).out
