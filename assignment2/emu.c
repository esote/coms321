/* emu is a LEGv8 emulator. */
#include <sys/mman.h>
#include <sys/stat.h>

#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

enum cond {
	C_EQ,
	C_NE,
	C_HS,
	C_LO,
	C_MI,
	C_PL,
	C_VS,
	C_VC,
	C_HI,
	C_LS,
	C_GE,
	C_LT,
	C_GT,
	C_LE
};

enum instruction_id {
	I_B,
	I_STURB,
	I_LDURB,
	I_B_COND,
	I_ORRI,
	I_EORI,
	I_STURH,
	I_LDURH,
	I_AND,
	I_ADD,
	I_ADDI,
	I_ANDI,
	I_BL,
	I_ORR,
	I_ADDS,
	I_ADDIS,
	I_CBZ,
	I_CBNZ,
	I_STURW,
	I_LDURSW,
	I_STXR,		/* ign */
	I_LDXR,		/* ign */
	I_EOR,
	I_SUB,
	I_SUBI,
	I_MOVZ,		/* ign */
	I_LSR,
	I_LSL,
	I_BR,
	I_ANDS,
	I_SUBS,
	I_SUBIS,
	I_ANDIS,
	I_MOVK,		/* ign */
	I_STUR,		/* ign: LDURD */
	I_LDUR,		/* ign: LDURS */

	I_MANY_FS,	/* ign: FADDS, FCMPS, FDIVS, FMULS, FSUBS */
	I_MANY_FD,	/* ign: FADDD, FCMPD, FDIVD, FMULD, FSUBD */
	I_MUL,
	I_MANY_DIV,
	I_SMULH,
	I_STURS,	/* ign */
	I_STURD,	/* ign */
	I_UMULH,

	I_PRNT,		/* custom */
	I_PRNL,		/* custom */
	I_DUMP,		/* custom */
	I_HALT		/* custom */
};

enum fmt {
	F_R,
	F_I,
	F_D,
	F_B,
	F_CB,
	F_IGN
};

union operands {
	uint32_t raw;
	struct {
		unsigned int rd : 5;
		unsigned int rn : 5;
		unsigned int shamt : 6;
		unsigned int rm : 5;
		unsigned int opcode : 11;
	} R;
	struct {
		unsigned int rd : 5;
		unsigned int rn : 5;
		unsigned int imm : 12;
		unsigned int opcode: 10;
	} I;
	struct {
		unsigned int rt : 5;
		unsigned int rn : 5;
		unsigned int op : 2;
		unsigned int dtaddr : 9;
		unsigned int opcode : 11;
	} D;
	struct {
		signed int braddr : 26;
		unsigned int opcode : 6;
	} B;
	struct {
		unsigned int rt : 5;
		signed int braddr : 19;
		unsigned int opcode : 8;
	} CB;
};

struct instruction {
	enum instruction_id id;
	enum fmt fmt;
	union operands ops;
};

static int		little_endian(void);
static uint32_t		swap(uint32_t);
static void		decode(uint32_t, struct instruction *);
static void		set_flag(enum cond, int);
static void		set_flags(int64_t);
static int		get_flag(enum cond);
static int		execute(size_t *, enum instruction_id, union operands *);
static void		chkregs(int, ...);
static void		mul(uint64_t, uint64_t, uint64_t *, uint64_t *);
static void		mem(union operands *, size_t, int);
static void		dump(void);
static unsigned char	printable(uint8_t);
static void		dump_mem(uint8_t *, size_t);
static char *		name(char *, unsigned int);
static void		prnt(unsigned int);
static void		disas(enum instruction_id, union operands *);
static void		data_hz(struct instruction *);

/* Subset of control signals. */
#define CTL_NULL	0
#define CTL_RegWrite	(1 << 0)
#define CTL_MemRead	(1 << 1)
#define CTL_LDUR	(CTL_RegWrite | CTL_MemRead)

#define OP_RANGE_L	48
static struct {
	uint32_t start;
	uint32_t end;
	enum fmt fmt;
	unsigned int ctl;
} op_range[OP_RANGE_L] = {
	{ 160, 191, F_B, CTL_NULL },		/* B */
	{ 448, 448, F_D, CTL_NULL },		/* STURB */
	{ 450, 450, F_D, CTL_LDUR },		/* LDURB */
	{ 672, 679, F_CB, CTL_NULL },		/* B.cond */
	{ 1424, 1425, F_I, CTL_RegWrite },	/* ORRI */
	{ 1680, 1681, F_I, CTL_RegWrite },	/* EORI */
	{ 960, 960, F_D, CTL_NULL },		/* STURH */
	{ 962, 962, F_D, CTL_LDUR },		/* LDURH */
	{ 1104, 1104, F_R, CTL_RegWrite },	/* AND */
	{ 1112, 1112, F_R, CTL_RegWrite },	/* ADD */
	{ 1160, 1161, F_I, CTL_RegWrite },	/* ADDI */
	{ 1168, 1169, F_I, CTL_RegWrite },	/* ANDI */
	{ 1184, 1215, F_B, CTL_NULL },		/* BL */
	{ 1360, 1360, F_R, CTL_RegWrite },	/* ORR */
	{ 1368, 1368, F_R, CTL_RegWrite },	/* ADDS */
	{ 1416, 1417, F_I, CTL_RegWrite },	/* ADDIS */
	{ 1440, 1447, F_CB, CTL_NULL },		/* CBZ */
	{ 1448, 1455, F_CB, CTL_NULL },		/* CBNZ */
	{ 1472, 1472, F_D, CTL_NULL },		/* STURW */
	{ 1476, 1476, F_D, CTL_LDUR },		/* LDURSW */
	{ 1600, 1600, F_IGN, CTL_NULL },	/* STXR */
	{ 1602, 1602, F_IGN, CTL_LDUR },	/* LDXR */
	{ 1616, 1616, F_R, CTL_RegWrite },	/* EOR */
	{ 1624, 1624, F_R, CTL_RegWrite },	/* SUB */
	{ 1672, 1673, F_I, CTL_RegWrite },	/* SUBI */
	{ 1684, 1687, F_IGN, CTL_NULL },	/* ign: MOVZ */
	{ 1690, 1690, F_R, CTL_RegWrite },	/* LSR */
	{ 1691, 1691, F_R, CTL_RegWrite },	/* LSL */
	{ 1712, 1712, F_R, CTL_NULL },		/* BR */
	{ 1872, 1872, F_R, CTL_RegWrite },	/* ANDS */
	{ 1880, 1880, F_R, CTL_RegWrite },	/* SUBS */
	{ 1928, 1929, F_I, CTL_RegWrite },	/* SUBIS */
	{ 1936, 1937, F_I, CTL_RegWrite },	/* ANDIS */
	{ 1940, 1943, F_IGN, CTL_NULL },	/* ign: MOVK */
	{ 1984, 1984, F_D, CTL_NULL },		/* STUR, ign: LDURD */
	{ 1986, 1986, F_D, CTL_LDUR },		/* LDUR, ign: LDURS */

	{ 241, 241, F_IGN, CTL_NULL },		/* ign: FADDS, FCMPS, FDIVS, FMULS, FSUBS */
	{ 243, 243, F_IGN, CTL_NULL },		/* ign: FADDD, FCMPD, FDIVD, FMULD, FSUBD */
	{ 1240, 1240, F_R, CTL_RegWrite },	/* MUL */
	{ 1238, 1238, F_R, CTL_RegWrite },	/* SDIV, UDIV */
	{ 1242, 1242, F_IGN, CTL_RegWrite},	/* SMULH */
	{ 2018, 2018, F_IGN, CTL_NULL },	/* ign: STURS */
	{ 2016, 2016, F_IGN, CTL_NULL },	/* ign: STURD */
	{ 1246, 1246, F_R, CTL_RegWrite },	/* UMULH */

	{ 1021, 1021, F_R, CTL_NULL },	/* PRNT, custom */
	{ 2044, 2044, F_R, CTL_NULL },	/* PRNL, custom */
	{ 2046, 2046, F_R, CTL_NULL },	/* DUMP, custom */
	{ 2047, 2047, F_R, CTL_NULL },	/* HALT, custom */
};

#define IP0	16
#define IP1	17
#define SP	28
#define FP	29
#define LR	30
#define XZR	31
static union {
	uint64_t u;
	int64_t s;
} regs[32];

#define PIPE_L	5
static struct instruction *pb[PIPE_L];

static struct {
	unsigned int cycles1;
	unsigned int cycles5;

	unsigned int loads;
	unsigned int stores;

	unsigned int data_hz;
	unsigned int data_by;

	unsigned int ctl_hz;
} stats;

static struct instruction *text;
static size_t text_l;

static uint16_t flags;

static size_t memory_l;
static size_t stack_l;
static uint8_t *memory;
static uint8_t *stack;

int
main(int argc, char *argv[])
{
	uint32_t *mapped;
	struct stat st;
	size_t i;
	char *end;
	int ch;
	int fd;

	memory_l = 4096;
	stack_l = 512;

	if (!little_endian()) {
		errx(1, "emulator requires a little-endian host");
	}

	while ((ch = getopt(argc, argv, "m:s:")) != -1) {
		switch (ch) {
		case 'm':
			memory_l = strtoull(optarg, &end, 0);
			if (errno == EINVAL || errno == ERANGE) {
				err(1, "memory size invalid");
			} else if (optarg == end) {
				errx(1, "no memory size read");
			}
			break;
		case 's':
			stack_l = strtoull(optarg, &end, 0);
			if (errno == EINVAL || errno == ERANGE) {
				err(1, "stack size invalid");
			} else if (optarg == end) {
				errx(1, "no stack size read");
			}
			break;
		default:
			(void)fprintf(stderr,
				"usage: %s [-m size] [-s size] file\n",
				argv[0]);
			return 1;
		}
	}

	argv += optind;

	if (*argv == NULL) {
		errx(1, "missing file argument");
	}

	if ((fd = open(*argv, O_RDONLY)) == -1) {
		err(1, "open %s", *argv);
	}

	if (fstat(fd, &st) == -1) {
		err(1, "fstat");
	}

	if (st.st_size == 0) {
		errx(1, "empty file");
	} else if (st.st_size % 4 != 0) {
		errx(1, "filesize should be modulus 4 for 32-bit instructions");
	}

	if ((mapped = mmap(NULL, (size_t)st.st_size, PROT_READ, MAP_PRIVATE, fd, 0)) == MAP_FAILED) {
		err(1, "mmap");
	}

	/* Closing fd does not unmap mapped. */
	if (close(fd) == -1) {
		err(1, "close");
	}

	text_l = (size_t)st.st_size / 4;
	if ((text = malloc(text_l * sizeof(struct instruction))) == NULL) {
		err(1, "malloc code segment");
	}

	/*
	Decode instruction: struct instruction uses bit fields to allow access
	to instruction components for each format.
	*/
	for (i = 0; i < text_l; i++) {
		decode(swap(mapped[i]), &text[i]);
	}

	if (munmap(mapped, (size_t)st.st_size) == -1) {
		err(1, "munmap");
	}

	if ((memory = calloc(memory_l, sizeof(uint8_t))) == NULL) {
		err(1, "calloc memory");
	}

	if ((stack = calloc(stack_l, sizeof(uint8_t))) == NULL) {
		err(1, "calloc stack");
	}

	memset(regs, 0, sizeof(regs));
	memset(pb, 0, sizeof(pb));
	memset(&stats, 0, sizeof(stats));
	i = 0;
	regs[SP].u = stack_l;
	regs[FP].u = stack_l;

	do {
		regs[XZR].u = 0;

		stats.cycles1++;
		data_hz(&text[i]);

		if (execute(&i, text[i].id, &text[i].ops)) {
			break;
		}
	} while (i < text_l);

	if (i > text_l + 1) {
		errx(1, "branch tried to leave emulator text segment");
	}

	/* Flush pipeline buffer to check for untested hazards. */
	while (pb[PIPE_L - 1] != NULL) {
		data_hz(NULL);
	}

	free(text);
	free(stack);
	free(memory);

	stats.cycles5 = stats.cycles1 + (PIPE_L - 1);

	(void)printf("End statistics:\n"
		"1-stage cycles: %u\n"
		"5-stage cycles without bypassing: %u\n"
		"Data hazards: %u\n"
		"Control hazards: %u\n"
		"5-stage cycles with bypassing: %u\n"
		"Loads: %u\n"
		"Stores: %u\n"
		"Stalls: %u\n"
		"Possible bypasses: %u\n",
		stats.cycles1,
		stats.cycles5 + stats.data_hz + 3 * stats.ctl_hz,
		stats.data_hz,
		stats.ctl_hz,
		stats.cycles5 + stats.data_hz + 3 * stats.ctl_hz - stats.data_by,
		stats.loads,
		stats.stores,
		stats.data_hz,
		stats.data_by);

	return EXIT_SUCCESS;
}

static int
little_endian(void)
{
	static union {
		uint32_t u32;
		uint8_t u8[4];
	} b = {0x01000000};
	return b.u8[3] == 1;
}

static uint32_t
swap(uint32_t x)
{
	/* With -O2 this assembles to the "bswap" instruction. */
	return ((x >> 24) & 0xff) | ((x << 8) & 0xff0000) | ((x >> 8) & 0xff00) | ((x << 24) & 0xff000000);
}

static void
decode(uint32_t raw, struct instruction *instr)
{
	uint32_t opcode;
	int i;

	opcode = raw >> (32 - 11);

	for (i = 0; i < OP_RANGE_L; i++) {
		if (opcode >= op_range[i].start && opcode <= op_range[i].end) {
			if (op_range[i].fmt == F_IGN) {
				errx(1, "instruction unsupported %08x", raw);
			}
			instr->id = (enum instruction_id)i;
			instr->fmt = op_range[i].fmt;
			instr->ops.raw = raw;
			return;
		}
	}

	errx(1, "illegal instruction %08x (11-bit opcode %"PRIu32")", raw,
		opcode);
}

static void
set_flag(enum cond c, int x)
{
	flags = (uint16_t)((flags & ~(1 << c)) | (x << c));
}

static void
set_flags(int64_t x)
{
	set_flag(C_EQ, x == 0);
	set_flag(C_NE, x != 0);
	set_flag(C_HS, x >= 0);
	set_flag(C_LO, x < 0);
	set_flag(C_MI, x < 0);
	set_flag(C_PL, x >= 0);
	set_flag(C_VS, 0);
	set_flag(C_VC, 0);
	set_flag(C_HI, x > 0);
	set_flag(C_LS, x <= 0);
	set_flag(C_GE, x >= 0);
	set_flag(C_LT, x < 0);
	set_flag(C_GT, x > 0);
	set_flag(C_LE, x <= 0);
}

static int
get_flag(enum cond c)
{
	return (flags >> c) & 1;
}

static int
execute(size_t *pc, enum instruction_id id, union operands *ops)
{
	(*pc)++;

	switch (id) {
	case I_B:
		*pc += (size_t)ops->B.braddr - 1;
		stats.ctl_hz += 1;
		break;
	case I_STURB:
		mem(ops, 1, 0);
		break;
	case I_LDURB:
		mem(ops, 1, 1);
		break;
	case I_B_COND:
		if (ops->CB.rt > 13) {
			errx(1, "condition flag %u invalid", ops->CB.rt);
		}
		if (get_flag((enum cond)ops->CB.rt)) {
			*pc += (size_t)ops->CB.braddr - 1;
			stats.ctl_hz += 1;
		}
		break;
	case I_ORRI:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u | ops->I.imm;
		break;
	case I_EORI:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u ^ ops->I.imm;
		break;
	case I_STURH:
		mem(ops, 2, 0);
		break;
	case I_LDURH:
		mem(ops, 2, 1);
		break;
	case I_AND:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u & regs[ops->R.rm].u;
		break;
	case I_ADD:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u + regs[ops->R.rm].u;
		break;
	case I_ADDI:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u + ops->I.imm;
		break;
	case I_ANDI:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u & ops->I.imm;
		break;
	case I_BL:
		regs[LR].u = (uint64_t)*pc;
		*pc += (size_t)ops->B.braddr - 1;
		stats.ctl_hz += 1;
		break;
	case I_ORR:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u | regs[ops->R.rm].u;
		break;
	case I_ADDS:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u + regs[ops->R.rm].u;
		set_flags(regs[ops->R.rd].s);
		break;
	case I_ADDIS:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u + ops->I.imm;
		set_flags(regs[ops->R.rd].s);
		break;
	case I_CBZ:
		chkregs(1, ops->CB.rt);
		if (regs[ops->CB.rt].u == 0) {
			*pc += (size_t)ops->CB.braddr - 1;
			stats.ctl_hz += 1;
		}
		break;
	case I_CBNZ:
		chkregs(1, ops->CB.rt);
		if (regs[ops->CB.rt].u != 0) {
			*pc += (size_t)ops->CB.braddr - 1;
			stats.ctl_hz += 1;
		}
		break;
	case I_STURW:
		mem(ops, 4, 0);
		break;
	case I_LDURSW:
		mem(ops, 4, 0);
		/* Sign-extend lower 32 bits */
		regs[ops->D.rn].u = (uint64_t)(int32_t)regs[ops->D.rn].u;
		break;
	case I_EOR:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u ^ regs[ops->R.rm].u;
		break;
	case I_SUB:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u - regs[ops->R.rm].u;
		break;
	case I_SUBI:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u - ops->I.imm;
		break;
	case I_LSR:
		chkregs(2, ops->R.rd, ops->R.rn);
		regs[ops->R.rd].u = regs[ops->R.rn].u >> ops->R.shamt;
		break;
	case I_LSL:
		chkregs(2, ops->R.rd, ops->R.rn);
		regs[ops->R.rd].u = regs[ops->R.rn].u << ops->R.shamt;
		break;
	case I_BR:
		chkregs(1, ops->R.rn);
		*pc = (size_t)regs[ops->R.rn].u;
		stats.ctl_hz += 1;
		break;
	case I_ANDS:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u & regs[ops->R.rm].u;
		set_flags(regs[ops->R.rd].s);
		break;
	case I_SUBS:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		regs[ops->R.rd].u = regs[ops->R.rn].u - regs[ops->R.rm].u;
		set_flags(regs[ops->R.rd].s);
		break;
	case I_SUBIS:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u - ops->I.imm;
		set_flags(regs[ops->I.rd].s);
		break;
	case I_ANDIS:
		chkregs(2, ops->I.rd, ops->I.rn);
		regs[ops->I.rd].u = regs[ops->I.rn].u & ops->I.imm;
		set_flags(regs[ops->R.rd].s);
		break;
	case I_STUR:
		mem(ops, 8, 0);
		break;
	case I_LDUR:
		mem(ops, 8, 1);
		break;
	case I_MUL:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		mul(regs[ops->R.rn].u, regs[ops->R.rm].u, NULL, &regs[ops->R.rd].u);
		break;
	case I_MANY_DIV:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		switch (ops->R.shamt) {
		case 0x03:
			regs[ops->R.rd].s = regs[ops->R.rn].s / regs[ops->R.rm].s;
			break;
		case 0x02:
			regs[ops->R.rd].s = regs[ops->R.rn].s / regs[ops->R.rm].s;
			break;
		default:
			errx(1, "div shamt %u invalid", ops->R.shamt);
		}
		break;
	case I_SMULH:
		/* FALLTHROUGH: sign will be in regs[ops->R.rd].s */
	case I_UMULH:
		chkregs(3, ops->R.rd, ops->R.rn, ops->R.rm);
		mul(regs[ops->R.rn].u, regs[ops->R.rm].u, &regs[ops->R.rd].u, NULL);
		break;
	case I_PRNT:
		chkregs(1, ops->R.rd);
		prnt(ops->R.rd);
		break;
	case I_PRNL:
		(void)putchar('\n');
		break;
	case I_DUMP:
		dump();
		break;
	case I_HALT:
		return 1;
	default:
		errx(1, "ignored instruction bypassed checks");
	}
	return 0;
}

static void
chkregs(int count, ...)
{
	va_list args;
	int x;
	va_start(args, count);
	for (; count > 0; count--) {
		x = va_arg(args, int);
		if (x > 31) {
			errx(1, "register X%u invalid", x);
		}
	}
	va_end(args);
}

static void
mul(uint64_t x, uint64_t y, uint64_t *hi, uint64_t *lo)
{
	uint64_t x1, y1;
	uint64_t t, k;
	uint64_t w1, w3;

	x1 = x & 0xffffffff;
	y1 = y & 0xffffffff;
	t = x1 * y1;
	w3 = t & 0xffffffff;
	k = t >> 32;

	x >>= 32;
	t = (x * y1) + k;
	k = t & 0xffffffff;
	w1 = t >> 32;

	y >>= 32;
	t = (y * x1) + k;
	k = t >> 32;

	if (hi != NULL) {
		*hi = x * y + w1 + k;
	}
	if (lo != NULL) {
		*lo = (t << 32) + w3;
	}
}

static void
mem(union operands *ops, size_t n, int load)
{
	char *name;
	size_t start;
	size_t end;
	size_t mem_l;
	uint8_t *mem;

	chkregs(2, ops->D.rn, ops->D.rt);

	if (ops->D.rn == SP || ops->D.rn == FP) {
		mem = stack;
		mem_l = stack_l;
		name = "stack";
	} else {
		mem = memory;
		mem_l = memory_l;
		name = "memory";
	}

	if (regs[ops->D.rn].s < 0) {
		errx(1, "SEGV: access to %s[%"PRId64":] bypasses %s size %zu",
			name, regs[ops->D.rn].s, name, mem_l);
	}

	start = regs[ops->D.rn].u + ops->D.dtaddr;
	end = start + n;

	if (end > mem_l) {
		errx(1, "SEGV: access to %s[%zu:%zu] bypasses %s size %zu",
			name, start, end, name, mem_l);
	}

	if (load) {
		memcpy(&regs[ops->D.rt], &mem[start], n);
		stats.loads++;
	} else {
		memcpy(&mem[start], &regs[ops->D.rt], n);
		stats.stores++;
	}
}

static void
dump(void)
{
	size_t i;

	(void)puts("Registers");
	for (i = 0; i < 32; i++) {
		prnt((unsigned int)i);
	}

	(void)puts("\nStack");
	dump_mem(stack, stack_l);

	(void)puts("\nMemory");
	dump_mem(memory, memory_l);

	(void)puts("\nDisassembly");
	for (i = 0; i < text_l; i++) {
		disas(text[i].id, &text[i].ops);
	}

	(void)putchar('\n');
}

static unsigned char
printable(uint8_t c)
{
	if (c >= ' ' && c <= '~') {
		return c;
	}
	return '.';
}

static void
dump_mem(uint8_t *m, size_t m_l)
{
	size_t i;
	for (i = 0; i < m_l - (m_l % 16); i += 16) {
		(void)printf("%08x: "
			"%02hx%02hx %02hx%02hx %02hx%02hx %02hx%02hx "
			"%02hx%02hx %02hx%02hx %02hx%02hx %02hx%02hx "
			"%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c\n",
			(uint32_t)i,
			m[i+7], m[i+6], m[i+5], m[i+4],
			m[i+3], m[i+2], m[i+1], m[i+0],
			m[i+15], m[i+14], m[i+13], m[i+12],
			m[i+11], m[i+10], m[i+9], m[i+8],
			printable(m[i+7]), printable(m[i+6]),
			printable(m[i+5]), printable(m[i+4]),
			printable(m[i+3]), printable(m[i+2]),
			printable(m[i+1]), printable(m[i+0]),
			printable(m[i+15]), printable(m[i+14]),
			printable(m[i+13]), printable(m[i+12]),
			printable(m[i+11]), printable(m[i+10]),
			printable(m[i+9]), printable(m[i+8]));
	}
	if (i != m_l) {
		warnx("dump does not include remaining %zu bytes", m_l % 16);
	}
}

#define NAME_L	4
static char *
name(char *s, unsigned int reg)
{
	switch (reg) {
	case IP0:
		strcpy(s, "IP0");
		break;
	case IP1:
		strcpy(s, "IP1");
		break;
	case SP:
		strcpy(s, "SP");
		break;
	case FP:
		strcpy(s, "FP");
		break;
	case LR:
		strcpy(s, "LR");
		break;
	case XZR:
		strcpy(s, "XZR");
		break;
	default:
		if (reg > 31) {
			strcpy(s, "X??");
			break;
		} else {
			sprintf(s, "X%u", reg);
		}
	}
	return s;
}

static void
prnt(unsigned int reg)
{
	static char s[NAME_L] = {0};
	(void)printf("%s: 0x%016"PRIx64" (%"PRIu64")\n", name(s, reg),
		regs[reg].u, regs[reg].u);
}

static void
disas(enum instruction_id id, union operands *ops)
{
	/* Buffer used when displaying pretty register names. */
	static char s[3][NAME_L] = {0};

	static char *cond[14] = {
		"EQ",
		"NE",
		"HS",
		"LO",
		"MI",
		"PL",
		"VS",
		"VC",
		"HI",
		"LS",
		"GE",
		"LT",
		"GT",
		"LE"
	};

	switch (id) {
	case I_B:
		(void)printf("B %d", ops->B.braddr);
		break;
	case I_STURB:
		(void)printf("STURB %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_LDURB:
		(void)printf("LDURB %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_B_COND:
		if (ops->CB.rt > 13) {
			errx(1, "condition flag %u invalid", ops->CB.rt);
		}
		(void)printf("B.%s %d", cond[ops->CB.rt], ops->CB.braddr);
		break;
	case I_ORRI:
		(void)printf("ORRI %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_EORI:
		(void)printf("EORI %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_STURH:
		(void)printf("STURH %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_LDURH:
		(void)printf("LDURH %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_AND:
		(void)printf("AND %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_ADD:
		(void)printf("ADD %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_ADDI:
		(void)printf("ADDI %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_ANDI:
		(void)printf("ANDI %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_BL:
		(void)printf("BL %d", ops->B.braddr);
		break;
	case I_ORR:
		(void)printf("ORR %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_ADDS:
		(void)printf("ANDS %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_ADDIS:
		(void)printf("ADDIS %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_CBZ:
		(void)printf("CBZ %s, %d", name(s[0], ops->CB.rt), ops->CB.braddr);
		break;
	case I_CBNZ:
		(void)printf("CBNZ %s, %d", name(s[0], ops->CB.rt),
			ops->CB.braddr);
		break;
	case I_STURW:
		(void)printf("STURW %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_LDURSW:
		(void)printf("LDURSW %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_EOR:
		(void)printf("EOR %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_SUB:
		(void)printf("SUB %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_SUBI:
		(void)printf("SUBI %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_LSR:
		(void)printf("LSR %s, %s, #%u", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), ops->R.shamt);
		break;
	case I_LSL:
		(void)printf("LSL %s, %s, #%u", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), ops->R.shamt);
		break;
	case I_BR:
		(void)printf("BR %s", name(s[0], ops->R.rn));
		break;
	case I_ANDS:
		(void)printf("ANDS %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_SUBS:
		(void)printf("SUBS %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_SUBIS:
		(void)printf("SUBIS %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_ANDIS:
		(void)printf("ANDIS %s, %s, #%u", name(s[0], ops->I.rd),
			name(s[1], ops->I.rn), ops->I.imm);
		break;
	case I_STUR:
		(void)printf("STUR %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_LDUR:
		(void)printf("LDUR %s, [%s, #%u]", name(s[0], ops->D.rt),
			name(s[1], ops->D.rn), ops->D.dtaddr);
		break;
	case I_MUL:
		(void)printf("MUL %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_MANY_DIV:
		switch (ops->R.shamt) {
		case 0x02:
			(void)printf("SDIV %s, %s, %s", name(s[0], ops->R.rd),
				name(s[1], ops->R.rn), name(s[2], ops->R.rm));
			break;
		case 0x03:
			(void)printf("UDIV %s, %s, %s", name(s[0], ops->R.rd),
				name(s[1], ops->R.rn), name(s[2], ops->R.rm));
			break;
		default:
			errx(1, "div shamt %u invalid", ops->R.shamt);
		}
		break;
	case I_SMULH:
		(void)printf("SMULH %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_UMULH:
		(void)printf("UMULH %s, %s, %s", name(s[0], ops->R.rd),
			name(s[1], ops->R.rn), name(s[2], ops->R.rm));
		break;
	case I_PRNT:
		(void)printf("PRNT %s", name(s[0], ops->R.rd));
		break;
	case I_PRNL:
		(void)printf("PRNL");
		break;
	case I_DUMP:
		(void)printf("DUMP <--- here");
		break;
	case I_HALT:
		(void)printf("HALT");
		break;
	default:
		errx(1, "ignored instruction bypassed checks");
	}
	(void)putchar('\n');
}

static void
data_hz(struct instruction *i)
{
#define IF_ID	(pb[0])
#define ID_EX	(pb[1])
#define EX_MEM	(pb[2])
#define MEM_WB	(pb[3])

	memmove(pb + 1, pb, (PIPE_L - 1) * sizeof(struct instruction *));
	IF_ID = i;

	if (ID_EX == NULL || EX_MEM == NULL || ID_EX->fmt == F_B) {
		return;
	}

#define MASK(r, m)	((op_range[(r)->id].ctl & (m)) == (m))

#define ONE_A	(EX_MEM != NULL		\
	&& MASK(EX_MEM, CTL_RegWrite)	\
	&& EX_MEM->ops.R.rd != XZR	\
	&& EX_MEM->ops.R.rd == ID_EX->ops.R.rn)

#define ONE_B	(EX_MEM != NULL		\
	&& MASK(EX_MEM, CTL_RegWrite)	\
	&& EX_MEM->ops.R.rd != XZR	\
	&& ID_EX->fmt != F_I		\
	&& EX_MEM->ops.R.rd == ID_EX->ops.R.rm)

#define TWO_A	(MEM_WB != NULL		\
	&& MASK(MEM_WB, CTL_RegWrite)	\
	&& MEM_WB->ops.R.rd != XZR	\
	/* && !(MASK(EX_MEM, CTL_RegWrite) && EX_MEM->ops.R.rd != XZR && EX_MEM->ops.R.rd != ID_EX->ops.R.rn) */\
	&& MEM_WB->ops.R.rd == ID_EX->ops.R.rn)

#define TWO_B	(MEM_WB != NULL		\
	&& MASK(MEM_WB, CTL_RegWrite)	\
	&& MEM_WB->ops.R.rd != XZR	\
	&& ID_EX->fmt != F_I		\
	/* && !(MASK(EX_MEM, CTL_RegWrite) && EX_MEM->ops.R.rd != XZR && EX_MEM->ops.R.rd != ID_EX->ops.R.rm) */\
	&& MEM_WB->ops.R.rd == ID_EX->ops.R.rm)

	if (ONE_A || ONE_B || TWO_A || TWO_B) {
		stats.data_hz++;
		stats.data_by++;
		return;
	}

	if (MASK(ID_EX, CTL_MemRead)
		&& ((ID_EX->ops.R.rd == IF_ID->ops.R.rn)
		|| (IF_ID->fmt != F_I && ID_EX->ops.R.rd == IF_ID->ops.R.rm))) {
		stats.data_hz++;
	}
}
