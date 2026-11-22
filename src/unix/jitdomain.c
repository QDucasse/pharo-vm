/*
 * RISC-V JITDomain: turns the extension on for the VM process, through the
 * PR_RISCV_JITDOMAIN prctl.
 *
 * VM code runs in domain 0, generated code in domain 1. For now both have
 * every right on every key, so the domain transitions in generated code are
 * checked (pads, labels, gates, the domain return stack) but no access is
 * restricted yet. Generated code still runs in domain 0 until the VM enters
 * it with domain calls, so its exits are domain calls from 0 to 0.
 */

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>

#include "pharovm/debug.h"

#define PR_RISCV_JITDOMAIN        0x4A444F4D  /* "JDOM" */
#define PR_JITDOMAIN_ENABLE       1
#define PR_JITDOMAIN_SET_MATRICES 2
#define PR_JITDOMAIN_DRS_ALLOC    4

#define JD_NDOMS  8
#define JD_DRSKEY 7         /* never accessible to any domain */
#define JD_RWX    7         /* {X, W, R} */

#define JD_DOM_VM  0
#define JD_DOM_JIT 1

struct jitdomain_matrices {
	uint64_t drights[3];    /* {X, W, R} per (domain, key), 3 bits each */
	uint64_t dtarget;       /* typed-access target per domain, 3 bits each */
	uint64_t dgate;         /* allowed domcall targets per domain, 8 bits each */
};

static void
setRights(struct jitdomain_matrices *m, unsigned dom, unsigned key, unsigned rights)
{
	for (unsigned b = 0; b < 3; b++) {
		unsigned bit = 3 * (JD_NDOMS * dom + key) + b;
		if ((rights >> b) & 1)
			m->drights[bit / 64] |= 1ULL << (bit % 64);
	}
}

static int
jdPrctl(unsigned long op, unsigned long arg)
{
	return prctl(PR_RISCV_JITDOMAIN, op, arg, 0, 0);
}

/* Once per process, before any domain instruction runs */
void
jitdomainEnable(void)
{
	struct jitdomain_matrices m;

	if (jdPrctl(PR_JITDOMAIN_ENABLE, 0)) {
		logError("JITDomain: PR_JITDOMAIN_ENABLE failed (%s); this VM needs a RISC-V hart with JITDomain",
			strerror(errno));
		exit(1);
	}

	memset(&m, 0, sizeof(m));
	for (unsigned key = 0; key < JD_DRSKEY; key++) {
		setRights(&m, JD_DOM_VM, key, JD_RWX);
		setRights(&m, JD_DOM_JIT, key, JD_RWX);
	}
	for (unsigned d = 0; d < JD_NDOMS; d++)
		m.dtarget |= (uint64_t)d << (3 * d);
	m.dgate = 1ULL << (8 * JD_DOM_VM + JD_DOM_JIT) | 1ULL << (8 * JD_DOM_JIT + JD_DOM_VM)
		| 1ULL << (8 * JD_DOM_VM + JD_DOM_VM);

	if (jdPrctl(PR_JITDOMAIN_SET_MATRICES, (unsigned long)&m)) {
		logError("JITDomain: PR_JITDOMAIN_SET_MATRICES failed (%s)", strerror(errno));
		exit(1);
	}
}

/* In each thread that runs Smalltalk: its domain return stack */
void
jitdomainThreadInit(void)
{
	if (jdPrctl(PR_JITDOMAIN_DRS_ALLOC, 0)) {
		logError("JITDomain: PR_JITDOMAIN_DRS_ALLOC failed (%s)", strerror(errno));
		exit(1);
	}
}
