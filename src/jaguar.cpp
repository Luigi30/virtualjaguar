//
// JAGUAR.CPP
//
// Originally by David Raingeard (Cal2)
// GCC/SDL port by Niels Wagenaar (Linux/WIN32) and Carwin Jones (BeOS)
// Cleanups and endian wrongness amelioration by James Hammons
// Note: Endian wrongness probably stems from the MAME origins of this emu and
//       the braindead way in which MAME handled memory when this was written. :-)
//
// JLH = James Hammons
//
// WHO  WHEN        WHAT
// ---  ----------  -----------------------------------------------------------
// JLH  11/25/2009  Major rewrite of memory subsystem and handlers
//

#include "jaguar.h"

#include <time.h>
#include <SDL.h>
#include "SDL_opengl.h"
#include "blitter.h"
#include "cdrom.h"
#include "dac.h"
#include "dsp.h"
#include "eeprom.h"
#include "event.h"
#include "foooked.h"
#include "gpu.h"
#include "jerry.h"
#include "joystick.h"
#include "log.h"
#include "m68000/m68kinterface.h"
//#include "memory.h"
#include "memtrack.h"
#include "mmu.h"
#include "settings.h"
#include "tom.h"

#define CPU_DEBUG
//Do this in makefile??? Yes! Could, but it's easier to define here...
//#define LOG_UNMAPPED_MEMORY_ACCESSES
//#define ABORT_ON_UNMAPPED_MEMORY_ACCESS
//#define ABORT_ON_ILLEGAL_INSTRUCTIONS
//#define ABORT_ON_OFFICIAL_ILLEGAL_INSTRUCTION
#define CPU_DEBUG_MEMORY
//#define LOG_CD_BIOS_CALLS
#define CPU_DEBUG_TRACING
#define ALPINE_FUNCTIONS

// Private function prototypes

unsigned jaguar_unknown_readbyte(unsigned address, uint32_t who = UNKNOWN);
unsigned jaguar_unknown_readword(unsigned address, uint32_t who = UNKNOWN);
void jaguar_unknown_writebyte(unsigned address, unsigned data, uint32_t who = UNKNOWN);
void jaguar_unknown_writeword(unsigned address, unsigned data, uint32_t who = UNKNOWN);
void M68K_show_context(void);

// External variables

#ifdef CPU_DEBUG_MEMORY
extern bool startMemLog;							// Set by "e" key
extern int effect_start;
extern int effect_start2, effect_start3, effect_start4, effect_start5, effect_start6;
#endif

// Really, need to include memory.h for this, but it might interfere with some stuff...
extern uint8_t jagMemSpace[];

// Internal variables

uint32_t jaguar_active_memory_dumps = 0;

uint32_t jaguarMainROMCRC32, jaguarROMSize, jaguarRunAddress;
bool jaguarCartInserted = false;
bool lowerField = false;

#ifdef CPU_DEBUG_MEMORY
uint8_t writeMemMax[0x400000], writeMemMin[0x400000];
uint8_t readMem[0x400000];
uint32_t returnAddr[4000], raPtr = 0xFFFFFFFF;
#endif

uint32_t pcQueue[0x400];
uint32_t a0Queue[0x400];
uint32_t a1Queue[0x400];
uint32_t a2Queue[0x400];
uint32_t a3Queue[0x400];
uint32_t a4Queue[0x400];
uint32_t a5Queue[0x400];
uint32_t a6Queue[0x400];
uint32_t a7Queue[0x400];
uint32_t d0Queue[0x400];
uint32_t d1Queue[0x400];
uint32_t d2Queue[0x400];
uint32_t d3Queue[0x400];
uint32_t d4Queue[0x400];
uint32_t d5Queue[0x400];
uint32_t d6Queue[0x400];
uint32_t d7Queue[0x400];
uint32_t srQueue[0x400];
uint32_t pcQPtr = 0;
bool startM68KTracing = false;

// Breakpoint on memory access vars (exported)
bool bpmActive = false;
uint32_t bpmAddress1;


//
// Callback function to detect illegal instructions
//
void GPUDumpDisassembly(void);
void GPUDumpRegisters(void);
static bool start = false;

void M68KInstructionHook(void)
{
	uint32_t m68kPC = m68k_get_reg(NULL, M68K_REG_PC);

// For code tracing...
#ifdef CPU_DEBUG_TRACING
	if (startM68KTracing)
	{
		static char buffer[2048];

		m68k_disassemble(buffer, m68kPC, 0);
		WriteLog("%06X: %s\n", m68kPC, buffer);
	}
#endif

// For tracebacks...
// Ideally, we'd save all the registers as well...
	pcQueue[pcQPtr] = m68kPC;
	a0Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A0);
	a1Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A1);
	a2Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A2);
	a3Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A3);
	a4Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A4);
	a5Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A5);
	a6Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A6);
	a7Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_A7);
	d0Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D0);
	d1Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D1);
	d2Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D2);
	d3Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D3);
	d4Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D4);
	d5Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D5);
	d6Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D6);
	d7Queue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_D7);
	srQueue[pcQPtr] = m68k_get_reg(NULL, M68K_REG_SR);
	pcQPtr++;
	pcQPtr &= 0x3FF;

	if (m68kPC & 0x01)		// Oops! We're fetching an odd address!
	{
		WriteLog("M68K: Attempted to execute from an odd address!\n\nBacktrace:\n\n");

		static char buffer[2048];
		for(int i=0; i<0x400; i++)
		{
			WriteLog("[A0=%08X, A1=%08X, A2=%08X, A3=%08X, A4=%08X, A5=%08X, A6=%08X, A7=%08X, D0=%08X, D1=%08X, D2=%08X, D3=%08X, D4=%08X, D5=%08X, D6=%08X, D7=%08X, SR=%04X]\n", a0Queue[(pcQPtr + i) & 0x3FF], a1Queue[(pcQPtr + i) & 0x3FF], a2Queue[(pcQPtr + i) & 0x3FF], a3Queue[(pcQPtr + i) & 0x3FF], a4Queue[(pcQPtr + i) & 0x3FF], a5Queue[(pcQPtr + i) & 0x3FF], a6Queue[(pcQPtr + i) & 0x3FF], a7Queue[(pcQPtr + i) & 0x3FF], d0Queue[(pcQPtr + i) & 0x3FF], d1Queue[(pcQPtr + i) & 0x3FF], d2Queue[(pcQPtr + i) & 0x3FF], d3Queue[(pcQPtr + i) & 0x3FF], d4Queue[(pcQPtr + i) & 0x3FF], d5Queue[(pcQPtr + i) & 0x3FF], d6Queue[(pcQPtr + i) & 0x3FF], d7Queue[(pcQPtr + i) & 0x3FF], srQueue[(pcQPtr + i) & 0x3FF]);
			m68k_disassemble(buffer, pcQueue[(pcQPtr + i) & 0x3FF], 0);//M68K_CPU_TYPE_68000);
			WriteLog("\t%08X: %s\n", pcQueue[(pcQPtr + i) & 0x3FF], buffer);
		}
		WriteLog("\n");

		uint32_t topOfStack = m68k_get_reg(NULL, M68K_REG_A7);
		WriteLog("M68K: Top of stack: %08X. Stack trace:\n", JaguarReadLong(topOfStack));
		for(int i=0; i<10; i++)
			WriteLog("%06X: %08X\n", topOfStack - (i * 4), JaguarReadLong(topOfStack - (i * 4)));
		WriteLog("Jaguar: VBL interrupt is %s\n", ((TOMIRQEnabled(IRQ_VIDEO)) && (JaguarInterruptHandlerIsValid(64))) ? "enabled" : "disabled");
		M68K_show_context();
		LogDone();
		exit(0);
	}

#ifdef LOG_CD_BIOS_CALLS
/*
CD_init::	-> $3000
BIOS_VER::	-> $3004
CD_mode::	-> $3006
CD_ack::	-> $300C
CD_jeri::	-> $3012
CD_spin::	-> $3018
CD_stop::	-> $301E
CD_mute::	-> $3024
CD_umute::	-> $302A
CD_paus::	-> $3030
CD_upaus::	-> $3036
CD_read::	-> $303C
CD_uread::	-> $3042
CD_setup::	-> $3048
CD_ptr::	-> $304E
CD_osamp::	-> $3054
CD_getoc::	-> $305A
CD_initm::	-> $3060
CD_initf::	-> $3066
CD_switch::	-> $306C
*/
	if (m68kPC == 0x3000)
		WriteLog("M68K: CD_init\n");
	else if (m68kPC == 0x3006 + (6 * 0))
		WriteLog("M68K: CD_mode\n");
	else if (m68kPC == 0x3006 + (6 * 1))
		WriteLog("M68K: CD_ack\n");
	else if (m68kPC == 0x3006 + (6 * 2))
		WriteLog("M68K: CD_jeri\n");
	else if (m68kPC == 0x3006 + (6 * 3))
		WriteLog("M68K: CD_spin\n");
	else if (m68kPC == 0x3006 + (6 * 4))
		WriteLog("M68K: CD_stop\n");
	else if (m68kPC == 0x3006 + (6 * 5))
		WriteLog("M68K: CD_mute\n");
	else if (m68kPC == 0x3006 + (6 * 6))
		WriteLog("M68K: CD_umute\n");
	else if (m68kPC == 0x3006 + (6 * 7))
		WriteLog("M68K: CD_paus\n");
	else if (m68kPC == 0x3006 + (6 * 8))
		WriteLog("M68K: CD_upaus\n");
	else if (m68kPC == 0x3006 + (6 * 9))
		WriteLog("M68K: CD_read\n");
	else if (m68kPC == 0x3006 + (6 * 10))
		WriteLog("M68K: CD_uread\n");
	else if (m68kPC == 0x3006 + (6 * 11))
		WriteLog("M68K: CD_setup\n");
	else if (m68kPC == 0x3006 + (6 * 12))
		WriteLog("M68K: CD_ptr\n");
	else if (m68kPC == 0x3006 + (6 * 13))
		WriteLog("M68K: CD_osamp\n");
	else if (m68kPC == 0x3006 + (6 * 14))
		WriteLog("M68K: CD_getoc\n");
	else if (m68kPC == 0x3006 + (6 * 15))
		WriteLog("M68K: CD_initm\n");
	else if (m68kPC == 0x3006 + (6 * 16))
		WriteLog("M68K: CD_initf\n");
	else if (m68kPC == 0x3006 + (6 * 17))
		WriteLog("M68K: CD_switch\n");

	if (m68kPC >= 0x3000 && m68kPC <= 0x306C)
		WriteLog("\t\tA0=%08X, A1=%08X, D0=%08X, D1=%08X, D2=%08X\n",
			m68k_get_reg(NULL, M68K_REG_A0), m68k_get_reg(NULL, M68K_REG_A1),
			m68k_get_reg(NULL, M68K_REG_D0), m68k_get_reg(NULL, M68K_REG_D1), m68k_get_reg(NULL, M68K_REG_D2));
#endif

#ifdef ABORT_ON_ILLEGAL_INSTRUCTIONS
	if (!m68k_is_valid_instruction(m68k_read_memory_16(m68kPC), 0))//M68K_CPU_TYPE_68000))
	{
#ifndef ABORT_ON_OFFICIAL_ILLEGAL_INSTRUCTION
		if (m68k_read_memory_16(m68kPC) == 0x4AFC)
		{
			// This is a kludge to let homebrew programs work properly (i.e., let the other processors
			// keep going even when the 68K dumped back to the debugger or what have you).
//dis no wok right!
//			m68k_set_reg(M68K_REG_PC, m68kPC - 2);
// Try setting the vector to the illegal instruction...
//This doesn't work right either! Do something else! Quick!
//			SET32(jaguar_mainRam, 0x10, m68kPC);

			return;
		}
#endif

		WriteLog("\nM68K encountered an illegal instruction at %08X!!!\n\nAborting!\n", m68kPC);
		uint32_t topOfStack = m68k_get_reg(NULL, M68K_REG_A7);
		WriteLog("M68K: Top of stack: %08X. Stack trace:\n", JaguarReadLong(topOfStack));
		uint32_t address = topOfStack - (4 * 4 * 3);

		for(int i=0; i<10; i++)
		{
			WriteLog("%06X:", address);

			for(int j=0; j<4; j++)
			{
				WriteLog(" %08X", JaguarReadLong(address));
				address += 4;
			}

			WriteLog("\n");
		}

		WriteLog("Jaguar: VBL interrupt is %s\n", ((TOMIRQEnabled(IRQ_VIDEO)) && (JaguarInterruptHandlerIsValid(64))) ? "enabled" : "disabled");
		M68K_show_context();

		LogDone();
		exit(0);
	}//*/
#endif
}

/*
  Now here be dragons...
  Here is how memory ranges are defined in the CoJag driver.
  Note that we only have to be concerned with 3 entities read/writing anything:
  The main CPU, the GPU, and the DSP. Everything else is unnecessary. So we can keep our main memory
  checking in jaguar.cpp, gpu.cpp and dsp.cpp. There should be NO checking in TOM, JERRY, etc. other than
  things that are entirely internal to those modules. This way we should be able to get a handle on all
  this crap which is currently scattered over Hells Half Acre(tm).

  Also: We need to distinguish whether or not we need .b, .w, and .dw versions of everything, or if there
  is a good way to collapse that shit (look below for inspiration). Current method works, but is error prone.
*/


/*
  JOYSTICK    $F14000               Read/Write
  15.....8  7......0
  Read        fedcba98  7654321q    f-1    Signals J15 to J1
  q      Cartridge EEPROM  output data
  Write       exxxxxxm  76543210    e      1 = enable  J7-J0 outputs
  0 = disable J7-J0 outputs
  x      don't care
  m      Audio mute
  0 = Audio muted (reset state)
  1 = Audio enabled
  7-4    J7-J4 outputs (port 2)
  3-0    J3-J0 outputs (port 1)
  JOYBUTS     $F14002               Read Only
  15.....8  7......0
  Read        xxxxxxxx  rrdv3210    x      don't care
  r      Reserved
  d      Reserved
  v      1 = NTSC Video hardware
  0 = PAL  Video hardware
  3-2    Button inputs B3 & B2 (port 2)
  1-0    Button inputs B1 & B0 (port 1)

  J4 J5 J6 J7  Port 2    B2     B3    J12  J13   J14  J15
  J3 J2 J1 J0  Port 1    B0     B1    J8   J9    J10  J11
  0  0  0  0
  0  0  0  1
  0  0  1  0
  0  0  1  1
  0  1  0  0
  0  1  0  1
  0  1  1  0
  0  1  1  1  Row 3     C3   Option  #     9     6     3
  1  0  0  0
  1  0  0  1
  1  0  1  0
  1  0  1  1  Row 2     C2      C    0     8     5     2
  1  1  0  0
  1  1  0  1  Row 1     C1      B    *     7     4     1
  1  1  1  0  Row 0   Pause     A    Up  Down  Left  Right
  1  1  1  1

  0 bit read in any position means that button is pressed.
  C3 = C2 = 1 means std. Jag. cntrlr. or nothing attached.
*/

void ShowM68KContext(void)
{
	printf("\t68K PC=%06X\n", m68k_get_reg(NULL, M68K_REG_PC));

	for(int i=M68K_REG_D0; i<=M68K_REG_D7; i++)
	{
		printf("D%i = %08X ", i-M68K_REG_D0, m68k_get_reg(NULL, (m68k_register_t)i));

		if (i == M68K_REG_D3 || i == M68K_REG_D7)
			printf("\n");
	}

	for(int i=M68K_REG_A0; i<=M68K_REG_A7; i++)
	{
		printf("A%i = %08X ", i-M68K_REG_A0, m68k_get_reg(NULL, (m68k_register_t)i));

		if (i == M68K_REG_A3 || i == M68K_REG_A7)
			printf("\n");
	}

	uint32_t currpc = m68k_get_reg(NULL, M68K_REG_PC);
	uint32_t disPC = currpc - 30;
	char buffer[128];

	do
	{
		uint32_t oldpc = disPC;
		disPC += m68k_disassemble(buffer, disPC, 0);
		printf("%s%08X: %s\n", (oldpc == currpc ? ">" : " "), oldpc, buffer);
	}
	while (disPC < (currpc + 10));
}


//
// Custom UAE 68000 read/write/IRQ functions
//

#if 0
IRQs:
=-=-=

      IPL         Name           Vector            Control
   ---------+---------------+---------------+---------------
       2      VBLANK IRQ         $100         INT1 bit #0 
       2      GPU IRQ            $100         INT1 bit #1
       2      HBLANK IRQ         $100         INT1 bit #2
       2      Timer IRQ          $100         INT1 bit #3

   Note: Both timer interrupts (JPIT && PIT) are on the same INT1 bit.
         and are therefore indistinguishable.

   A typical way to install a LEVEL2 handler for the 68000 would be 
   something like this, you gotta supply "last_line" and "handler".
   Note that the interrupt is auto vectored thru $100 (not $68)


   V_AUTO   = $100
   VI       = $F004E
   INT1     = $F00E0
   INT2     = $F00E2
   
   IRQS_HANDLED=$909                ;; VBLANK and TIMER

         move.w   #$2700,sr         ;; no IRQs please
         move.l   #handler,V_AUTO   ;; install our routine

         move.w   #last_line,VI     ;; scanline where IRQ should occur
                                    ;; should be 'odd' BTW
         move.w   #IRQS_HANDLE&$FF,INT1  ;; enable VBLANK + TIMER
         move.w   #$2100,sr         ;; enable IRQs on the 68K
         ...

handler:
         move.w   d0,-(a7)
         move.w   INT1,d0
         btst.b   #0,d0
         bne.b    .no_blank

         ...

.no_blank:
         btst.b   #3,d0
         beq.b    .no_timer
      
         ...

.no_timer:
         move.w   #IRQS_HANDLED,INT1      ; clear latch, keep IRQ alive
         move.w   #0,INT2                 ; let GPU run again
         move.w   (a7)+,d0
         rte

   As you can see, if you have multiple INT1 interrupts coming in,
   you need to check the lower byte of INT1, to see which interrupt
   happened.
#endif
int irq_ack_handler(int level)
{
#ifdef CPU_DEBUG_TRACING
	if (startM68KTracing)
	{
		WriteLog("irq_ack_handler: M68K PC=%06X\n", m68k_get_reg(NULL, M68K_REG_PC));
	}
#endif

	// Tracing the IPL lines on the Jaguar schematic yields the following:
	// IPL1 is connected to INTL on TOM (OUT to 68K)
	// IPL0-2 are also tied to Vcc via 4.7K resistors!
	// (DINT on TOM goes into DINT on JERRY (IN Tom from Jerry))
	// There doesn't seem to be any other path to IPL0 or 2 on the schematic,
	// which means that *all* IRQs to the 68K are routed thru TOM at level 2.
	// Which means they're all maskable.

	// The GPU/DSP/etc are probably *not* issuing an NMI, but it seems to work
	// OK...
	// They aren't, and this causes problems with a, err, specific ROM. :-D

	if (level == 2)
	{
		m68k_set_irq(0);						// Clear the IRQ (NOTE: Without this, the BIOS fails)...
		return 64;								// Set user interrupt #0
	}

	return M68K_INT_ACK_AUTOVECTOR;
}


//#define USE_NEW_MMU

unsigned int m68k_read_memory_8(unsigned int address)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
#ifdef CPU_DEBUG_MEMORY
	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFF))
	{
		if (startMemLog)
			readMem[address] = 1;
	}
#endif
//WriteLog("[RM8] Addr: %08X\n", address);
//; So, it seems that it stores the returned DWORD at $51136 and $FB074.
/*	if (address == 0x51136 || address == 0x51138 || address == 0xFB074 || address == 0xFB076
		|| address == 0x1AF05E)
		WriteLog("[RM8  PC=%08X] Addr: %08X, val: %02X\n", m68k_get_reg(NULL, M68K_REG_PC), address, jaguar_mainRam[address]);//*/
#ifndef USE_NEW_MMU
	unsigned int retVal = 0;

	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFF))
		retVal = jaguarMainRAM[address];
//	else if ((address >= 0x800000) && (address <= 0xDFFFFF))
	else if ((address >= 0x800000) && (address <= 0xDFFEFF))
		retVal = jaguarMainROM[address - 0x800000];
	else if ((address >= 0xE00000) && (address <= 0xE3FFFF))
//		retVal = jaguarBootROM[address - 0xE00000];
//		retVal = jaguarDevBootROM1[address - 0xE00000];
		retVal = jagMemSpace[address];
	else if ((address >= 0xDFFF00) && (address <= 0xDFFFFF))
		retVal = CDROMReadByte(address);
	else if ((address >= 0xF00000) && (address <= 0xF0FFFF))
		retVal = TOMReadByte(address, M68K);
	else if ((address >= 0xF10000) && (address <= 0xF1FFFF))
		retVal = JERRYReadByte(address, M68K);
	else
		retVal = jaguar_unknown_readbyte(address, M68K);

//if (address >= 0x2800 && address <= 0x281F)
//	WriteLog("M68K: Read byte $%02X at $%08X [PC=%08X]\n", retVal, address, m68k_get_reg(NULL, M68K_REG_PC));
//if (address >= 0x8B5E4 && address <= 0x8B5E4 + 16)
//	WriteLog("M68K: Read byte $%02X at $%08X [PC=%08X]\n", retVal, address, m68k_get_reg(NULL, M68K_REG_PC));
    return retVal;
#else
	return MMURead8(address, M68K);
#endif
}


void gpu_dump_disassembly(void);
void gpu_dump_registers(void);

unsigned int m68k_read_memory_16(unsigned int address)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
#ifdef CPU_DEBUG_MEMORY
/*	if ((address >= 0x000000) && (address <= 0x3FFFFE))
	{
		if (startMemLog)
			readMem[address] = 1, readMem[address + 1] = 1;
	}//*/
/*	if (effect_start && (address >= 0x8064FC && address <= 0x806501))
	{
		return 0x4E71;	// NOP
	}
	if (effect_start2 && (address >= 0x806502 && address <= 0x806507))
	{
		return 0x4E71;	// NOP
	}
	if (effect_start3 && (address >= 0x806512 && address <= 0x806517))
	{
		return 0x4E71;	// NOP
	}
	if (effect_start4 && (address >= 0x806524 && address <= 0x806527))
	{
		return 0x4E71;	// NOP
	}
	if (effect_start5 && (address >= 0x80653E && address <= 0x806543)) //Collision detection!
	{
		return 0x4E71;	// NOP
	}
	if (effect_start6 && (address >= 0x806544 && address <= 0x806547))
	{
		return 0x4E71;	// NOP
	}//*/
#endif
//WriteLog("[RM16] Addr: %08X\n", address);
/*if (m68k_get_reg(NULL, M68K_REG_PC) == 0x00005FBA)
//	for(int i=0; i<10000; i++)
	WriteLog("[M68K] In routine #6!\n");//*/
//if (m68k_get_reg(NULL, M68K_REG_PC) == 0x00006696) // GPU Program #4
//if (m68k_get_reg(NULL, M68K_REG_PC) == 0x00005B3C)	// GPU Program #2
/*if (m68k_get_reg(NULL, M68K_REG_PC) == 0x00005BA8)	// GPU Program #3
{
	WriteLog("[M68K] About to run GPU! (Addr:%08X, data:%04X)\n", address, TOMReadWord(address));
	gpu_dump_registers();
	gpu_dump_disassembly();
//	for(int i=0; i<10000; i++)
//		WriteLog("[M68K] About to run GPU!\n");
}//*/
//WriteLog("[WM8  PC=%08X] Addr: %08X, val: %02X\n", m68k_get_reg(NULL, M68K_REG_PC), address, value);
/*if (m68k_get_reg(NULL, M68K_REG_PC) >= 0x00006696 && m68k_get_reg(NULL, M68K_REG_PC) <= 0x000066A8)
{
	if (address == 0x000066A0)
	{
		gpu_dump_registers();
		gpu_dump_disassembly();
	}
	for(int i=0; i<10000; i++)
		WriteLog("[M68K] About to run GPU! (Addr:%08X, data:%04X)\n", address, TOMReadWord(address));
}//*/
//; So, it seems that it stores the returned DWORD at $51136 and $FB074.
/*	if (address == 0x51136 || address == 0x51138 || address == 0xFB074 || address == 0xFB076
		|| address == 0x1AF05E)
		WriteLog("[RM16  PC=%08X] Addr: %08X, val: %04X\n", m68k_get_reg(NULL, M68K_REG_PC), address, GET16(jaguar_mainRam, address));//*/
#ifndef USE_NEW_MMU
    unsigned int retVal = 0;

	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFE))
//		retVal = (jaguar_mainRam[address] << 8) | jaguar_mainRam[address+1];
		retVal = GET16(jaguarMainRAM, address);
//	else if ((address >= 0x800000) && (address <= 0xDFFFFE))
	else if ((address >= 0x800000) && (address <= 0xDFFEFE))
	{
		// Memory Track reading...
		if (((TOMGetMEMCON1() & 0x0006) == (2 << 1)) && (jaguarMainROMCRC32 == 0xFDF37F47))
		{
			retVal = MTReadWord(address);
		}
		else
			retVal = (jaguarMainROM[address - 0x800000] << 8)
				| jaguarMainROM[address - 0x800000 + 1];
	}
	else if ((address >= 0xE00000) && (address <= 0xE3FFFE))
//		retVal = (jaguarBootROM[address - 0xE00000] << 8) | jaguarBootROM[address - 0xE00000 + 1];
//		retVal = (jaguarDevBootROM1[address - 0xE00000] << 8) | jaguarDevBootROM1[address - 0xE00000 + 1];
		retVal = (jagMemSpace[address] << 8) | jagMemSpace[address + 1];
	else if ((address >= 0xDFFF00) && (address <= 0xDFFFFE))
		retVal = CDROMReadWord(address, M68K);
	else if ((address >= 0xF00000) && (address <= 0xF0FFFE))
		retVal = TOMReadWord(address, M68K);
	else if ((address >= 0xF10000) && (address <= 0xF1FFFE))
		retVal = JERRYReadWord(address, M68K);
	else
		retVal = jaguar_unknown_readword(address, M68K);

//if (address >= 0xF1B000 && address <= 0xF1CFFF)
//	WriteLog("M68K: Read word $%04X at $%08X [PC=%08X]\n", retVal, address, m68k_get_reg(NULL, M68K_REG_PC));
//if (address >= 0x2800 && address <= 0x281F)
//	WriteLog("M68K: Read word $%04X at $%08X [PC=%08X]\n", retVal, address, m68k_get_reg(NULL, M68K_REG_PC));
//$8B3AE -> Transferred from $F1C010
//$8B5E4 -> Only +1 read at $808AA
//if (address >= 0x8B5E4 && address <= 0x8B5E4 + 16)
//	WriteLog("M68K: Read word $%04X at $%08X [PC=%08X]\n", retVal, address, m68k_get_reg(NULL, M68K_REG_PC));
    return retVal;
#else
	return MMURead16(address, M68K);
#endif
}


unsigned int m68k_read_memory_32(unsigned int address)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
//; So, it seems that it stores the returned DWORD at $51136 and $FB074.
/*	if (address == 0x51136 || address == 0xFB074 || address == 0x1AF05E)
		WriteLog("[RM32  PC=%08X] Addr: %08X, val: %08X\n", m68k_get_reg(NULL, M68K_REG_PC), address, (m68k_read_memory_16(address) << 16) | m68k_read_memory_16(address + 2));//*/

//WriteLog("--> [RM32]\n");
#ifndef USE_NEW_MMU
	uint32_t retVal = 0;

	if ((address >= 0x800000) && (address <= 0xDFFEFE))
	{
		// Memory Track reading...
		if (((TOMGetMEMCON1() & 0x0006) == (2 << 1)) && (jaguarMainROMCRC32 == 0xFDF37F47))
			retVal = MTReadLong(address);
		else
			retVal = GET32(jaguarMainROM, address - 0x800000);

		return retVal;
	}

	return (m68k_read_memory_16(address) << 16) | m68k_read_memory_16(address + 2);
#else
	return MMURead32(address, M68K);
#endif
}


void m68k_write_memory_8(unsigned int address, unsigned int value)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
#ifdef CPU_DEBUG_MEMORY
	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFF))
	{
		if (startMemLog)
		{
			if (value > writeMemMax[address])
				writeMemMax[address] = value;
			if (value < writeMemMin[address])
				writeMemMin[address] = value;
		}
	}
#endif
/*if (address == 0x4E00)
	WriteLog("M68K: Writing %02X at %08X, PC=%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));//*/
//if ((address >= 0x1FF020 && address <= 0x1FF03F) || (address >= 0x1FF820 && address <= 0x1FF83F))
//	WriteLog("M68K: Writing %02X at %08X\n", value, address);
//WriteLog("[WM8  PC=%08X] Addr: %08X, val: %02X\n", m68k_get_reg(NULL, M68K_REG_PC), address, value);
/*if (effect_start)
	if (address >= 0x18FA70 && address < (0x18FA70 + 8000))
		WriteLog("M68K: Byte %02X written at %08X by 68K\n", value, address);//*/
//$53D0
/*if (address >= 0x53D0 && address <= 0x53FF)
	printf("M68K: Writing byte $%02X at $%08X, PC=$%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));//*/
//Testing AvP on UAE core...
//000075A0: FFFFF80E B6320220 (BITMAP)
/*if (address == 0x75A0 && value == 0xFF)
	printf("M68K: (8) Tripwire hit...\n");//*/

#ifndef USE_NEW_MMU
	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFF))
		jaguarMainRAM[address] = value;
	else if ((address >= 0xDFFF00) && (address <= 0xDFFFFF))
		CDROMWriteByte(address, value, M68K);
	else if ((address >= 0xF00000) && (address <= 0xF0FFFF))
		TOMWriteByte(address, value, M68K);
	else if ((address >= 0xF10000) && (address <= 0xF1FFFF))
		JERRYWriteByte(address, value, M68K);
	else
		jaguar_unknown_writebyte(address, value, M68K);
#else
	MMUWrite8(address, value, M68K);
#endif
}


void m68k_write_memory_16(unsigned int address, unsigned int value)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
#ifdef CPU_DEBUG_MEMORY
	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFE))
	{
		if (startMemLog)
		{
			uint8_t hi = value >> 8, lo = value & 0xFF;

			if (hi > writeMemMax[address])
				writeMemMax[address] = hi;
			if (hi < writeMemMin[address])
				writeMemMin[address] = hi;

			if (lo > writeMemMax[address+1])
				writeMemMax[address+1] = lo;
			if (lo < writeMemMin[address+1])
				writeMemMin[address+1] = lo;
		}
	}
#endif
/*if (address == 0x4E00)
	WriteLog("M68K: Writing %02X at %08X, PC=%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));//*/
//if ((address >= 0x1FF020 && address <= 0x1FF03F) || (address >= 0x1FF820 && address <= 0x1FF83F))
//	WriteLog("M68K: Writing %04X at %08X\n", value, address);
//WriteLog("[WM16 PC=%08X] Addr: %08X, val: %04X\n", m68k_get_reg(NULL, M68K_REG_PC), address, value);
//if (address >= 0xF02200 && address <= 0xF0229F)
//	WriteLog("M68K: Writing to blitter --> %04X at %08X\n", value, address);
//if (address >= 0x0E75D0 && address <= 0x0E75E7)
//	WriteLog("M68K: Writing %04X at %08X, M68K PC=%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));
/*extern uint32_t totalFrames;
if (address == 0xF02114)
	WriteLog("M68K: Writing to GPU_CTRL (frame:%u)... [M68K PC:%08X]\n", totalFrames, m68k_get_reg(NULL, M68K_REG_PC));
if (address == 0xF02110)
	WriteLog("M68K: Writing to GPU_PC (frame:%u)... [M68K PC:%08X]\n", totalFrames, m68k_get_reg(NULL, M68K_REG_PC));//*/
//if (address >= 0xF03B00 && address <= 0xF03DFF)
//	WriteLog("M68K: Writing %04X to %08X...\n", value, address);

/*if (address == 0x0100)//64*4)
	WriteLog("M68K: Wrote word to VI vector value %04X...\n", value);//*/
/*if (effect_start)
	if (address >= 0x18FA70 && address < (0x18FA70 + 8000))
		WriteLog("M68K: Word %04X written at %08X by 68K\n", value, address);//*/
/*	if (address == 0x51136 || address == 0x51138 || address == 0xFB074 || address == 0xFB076
		|| address == 0x1AF05E)
		WriteLog("[WM16  PC=%08X] Addr: %08X, val: %04X\n", m68k_get_reg(NULL, M68K_REG_PC), address, value);//*/
//$53D0
/*if (address >= 0x53D0 && address <= 0x53FF)
	printf("M68K: Writing word $%04X at $%08X, PC=$%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));//*/
//Testing AvP on UAE core...
//000075A0: FFFFF80E B6320220 (BITMAP)
/*if (address == 0x75A0 && value == 0xFFFF)
{
	printf("\nM68K: (16) Tripwire hit...\n");
	ShowM68KContext();
}//*/

#ifndef USE_NEW_MMU
	// Note that the Jaguar only has 2M of RAM, not 4!
	if ((address >= 0x000000) && (address <= 0x1FFFFE))
	{
/*		jaguar_mainRam[address] = value >> 8;
		jaguar_mainRam[address + 1] = value & 0xFF;*/
		SET16(jaguarMainRAM, address, value);
	}
	// Memory Track device writes....
	else if ((address >= 0x800000) && (address <= 0x87FFFE))
	{
		if (((TOMGetMEMCON1() & 0x0006) == (2 << 1)) && (jaguarMainROMCRC32 == 0xFDF37F47))
			MTWriteWord(address, value);
	}
	else if ((address >= 0xDFFF00) && (address <= 0xDFFFFE))
		CDROMWriteWord(address, value, M68K);
	else if ((address >= 0xF00000) && (address <= 0xF0FFFE))
		TOMWriteWord(address, value, M68K);
	else if ((address >= 0xF10000) && (address <= 0xF1FFFE))
		JERRYWriteWord(address, value, M68K);
	else
	{
		jaguar_unknown_writeword(address, value, M68K);
#ifdef LOG_UNMAPPED_MEMORY_ACCESSES
		WriteLog("\tA0=%08X, A1=%08X, D0=%08X, D1=%08X\n",
			m68k_get_reg(NULL, M68K_REG_A0), m68k_get_reg(NULL, M68K_REG_A1),
			m68k_get_reg(NULL, M68K_REG_D0), m68k_get_reg(NULL, M68K_REG_D1));
#endif
	}
#else
	MMUWrite16(address, value, M68K);
#endif
}


void m68k_write_memory_32(unsigned int address, unsigned int value)
{
#ifdef ALPINE_FUNCTIONS
	// Check if breakpoint on memory is active, and deal with it
	if (bpmActive && address == bpmAddress1)
		M68KDebugHalt();
#endif

	// Musashi does this automagically for you, UAE core does not :-P
	address &= 0x00FFFFFF;
/*if (address == 0x4E00)
	WriteLog("M68K: Writing %02X at %08X, PC=%08X\n", value, address, m68k_get_reg(NULL, M68K_REG_PC));//*/
//WriteLog("--> [WM32]\n");
/*if (address == 0x0100)//64*4)
	WriteLog("M68K: Wrote dword to VI vector value %08X...\n", value);//*/
/*if (address >= 0xF03214 && address < 0xF0321F)
	WriteLog("M68K: Writing DWORD (%08X) to GPU RAM (%08X)...\n", value, address);//*/
//M68K: Writing DWORD (88E30047) to GPU RAM (00F03214)...
/*extern bool doGPUDis;
if (address == 0xF03214 && value == 0x88E30047)
//	start = true;
	doGPUDis = true;//*/
/*	if (address == 0x51136 || address == 0xFB074)
		WriteLog("[WM32  PC=%08X] Addr: %08X, val: %02X\n", m68k_get_reg(NULL, M68K_REG_PC), address, value);//*/
//Testing AvP on UAE core...
//000075A0: FFFFF80E B6320220 (BITMAP)
/*if (address == 0x75A0 && (value & 0xFFFF0000) == 0xFFFF0000)
{
	printf("\nM68K: (32) Tripwire hit...\n");
	ShowM68KContext();
}//*/

#ifndef USE_NEW_MMU
	m68k_write_memory_16(address, value >> 16);
	m68k_write_memory_16(address + 2, value & 0xFFFF);
#else
	MMUWrite32(address, value, M68K);
#endif
}


uint32_t JaguarGetHandler(uint32_t i)
{
	return JaguarReadLong(i * 4);
}


bool JaguarInterruptHandlerIsValid(uint32_t i) // Debug use only...
{
	uint32_t handler = JaguarGetHandler(i);
	return (handler && (handler != 0xFFFFFFFF) ? true : false);
}


void M68K_show_context(void)
{
	WriteLog("68K PC=%06X\n", m68k_get_reg(NULL, M68K_REG_PC));

	for(int i=M68K_REG_D0; i<=M68K_REG_D7; i++)
	{
		WriteLog("D%i = %08X ", i-M68K_REG_D0, m68k_get_reg(NULL, (m68k_register_t)i));

		if (i == M68K_REG_D3 || i == M68K_REG_D7)
			WriteLog("\n");
	}

	for(int i=M68K_REG_A0; i<=M68K_REG_A7; i++)
	{
		WriteLog("A%i = %08X ", i-M68K_REG_A0, m68k_get_reg(NULL, (m68k_register_t)i));

		if (i == M68K_REG_A3 || i == M68K_REG_A7)
			WriteLog("\n");
	}

	WriteLog("68K disasm\n");
//	jaguar_dasm(s68000readPC()-0x1000,0x20000);
	JaguarDasm(m68k_get_reg(NULL, M68K_REG_PC) - 0x80, 0x200);
//	jaguar_dasm(0x5000, 0x14414);

//	WriteLog("\n.......[Cart start]...........\n\n");
//	jaguar_dasm(0x192000, 0x1000);//0x200);

	WriteLog("..................\n");

	if (TOMIRQEnabled(IRQ_VIDEO))
	{
		WriteLog("video int: enabled\n");
		JaguarDasm(JaguarGetHandler(64), 0x200);
	}
	else
		WriteLog("video int: disabled\n");

	WriteLog("..................\n");

	for(int i=0; i<256; i++)
	{
		WriteLog("handler %03i at ", i);//$%08X\n", i, (unsigned int)JaguarGetHandler(i));
		uint32_t address = (uint32_t)JaguarGetHandler(i);

		if (address == 0)
			WriteLog(".........\n");
		else
			WriteLog("$%08X\n", address);
	}
}


//
// Unknown read/write byte/word routines
//

// It's hard to believe that developers would be sloppy with their memory
// writes, yet in some cases the developers screwed up royal. E.g., Club Drive
// has the following code:
//
// 807EC4: movea.l #$f1b000, A1
// 807ECA: movea.l #$8129e0, A0
// 807ED0: move.l  A0, D0
// 807ED2: move.l  #$f1bb94, D1
// 807ED8: sub.l   D0, D1
// 807EDA: lsr.l   #2, D1
// 807EDC: move.l  (A0)+, (A1)+
// 807EDE: dbra    D1, 807edc
//
// The problem is at $807ED0--instead of putting A0 into D0, they really meant
// to put A1 in. This mistake causes it to try and overwrite approximately
// $700000 worth of address space! (That is, unless the 68K causes a bus
// error...)

void jaguar_unknown_writebyte(unsigned address, unsigned data, uint32_t who/*=UNKNOWN*/)
{
  if(address == 0x800000)
    FakeSkunkLogByte(data & 0xFF); //This is a fake skunkboard console.
  
#ifdef LOG_UNMAPPED_MEMORY_ACCESSES
     WriteLog("Jaguar: Unknown byte %02X written at %08X by %s (M68K PC=%06X)\n", data, address, whoName[who], m68k_get_reg(NULL, M68K_REG_PC));
#endif
#ifdef ABORT_ON_UNMAPPED_MEMORY_ACCESS
     //	extern bool finished;
     finished = true;
     //	extern bool doDSPDis;
     if (who == DSP)
       doDSPDis = true;
#endif
}


void jaguar_unknown_writeword(unsigned address, unsigned data, uint32_t who/*=UNKNOWN*/)
{
#ifdef LOG_UNMAPPED_MEMORY_ACCESSES
	WriteLog("Jaguar: Unknown word %04X written at %08X by %s (M68K PC=%06X)\n", data, address, whoName[who], m68k_get_reg(NULL, M68K_REG_PC));
#endif
#ifdef ABORT_ON_UNMAPPED_MEMORY_ACCESS
	finished = true;
	if (who == DSP)
		doDSPDis = true;
#endif
}


unsigned jaguar_unknown_readbyte(unsigned address, uint32_t who/*=UNKNOWN*/)
{
#ifdef LOG_UNMAPPED_MEMORY_ACCESSES
	WriteLog("Jaguar: Unknown byte read at %08X by %s (M68K PC=%06X)\n", address, whoName[who], m68k_get_reg(NULL, M68K_REG_PC));
#endif
#ifdef ABORT_ON_UNMAPPED_MEMORY_ACCESS
	finished = true;
	if (who == DSP)
		doDSPDis = true;
#endif
    return 0xFF;
}


unsigned jaguar_unknown_readword(unsigned address, uint32_t who/*=UNKNOWN*/)
{
#ifdef LOG_UNMAPPED_MEMORY_ACCESSES
	WriteLog("Jaguar: Unknown word read at %08X by %s (M68K PC=%06X)\n", address, whoName[who], m68k_get_reg(NULL, M68K_REG_PC));
#endif
#ifdef ABORT_ON_UNMAPPED_MEMORY_ACCESS
	finished = true;
	if (who == DSP)
		doDSPDis = true;
#endif
    return 0xFFFF;
}


//
// Disassemble M68K instructions at the given offset
//

unsigned int m68k_read_disassembler_8(unsigned int address)
{
	return m68k_read_memory_8(address);
}


unsigned int m68k_read_disassembler_16(unsigned int address)
{
	return m68k_read_memory_16(address);
}


unsigned int m68k_read_disassembler_32(unsigned int address)
{
	return m68k_read_memory_32(address);
}


void JaguarDasm(uint32_t offset, uint32_t qt)
{
#ifdef CPU_DEBUG
	static char buffer[2048];
	int pc = offset, oldpc;

	for(uint32_t i=0; i<qt; i++)
	{
		oldpc = pc;
		pc += m68k_disassemble(buffer, pc, 0);
		WriteLog("%08X: %s\n", oldpc, buffer);
	}
#endif
}


uint8_t JaguarReadByte(uint32_t offset, uint32_t who/*=UNKNOWN*/)
{
	uint8_t data = 0x00;
	offset &= 0xFFFFFF;

	// First 2M is mirrored in the $0 - $7FFFFF range
	if (offset < 0x800000)
		data = jaguarMainRAM[offset & 0x1FFFFF];
	else if ((offset >= 0x800000) && (offset < 0xDFFF00))
		data = jaguarMainROM[offset - 0x800000];
	else if ((offset >= 0xDFFF00) && (offset <= 0xDFFFFF))
		data = CDROMReadByte(offset, who);
	else if ((offset >= 0xE00000) && (offset < 0xE40000))
		data = jagMemSpace[offset];
	else if ((offset >= 0xF00000) && (offset < 0xF10000))
		data = TOMReadByte(offset, who);
	else if ((offset >= 0xF10000) && (offset < 0xF20000))
		data = JERRYReadByte(offset, who);
	else
		data = jaguar_unknown_readbyte(offset, who);

	return data;
}


uint16_t JaguarReadWord(uint32_t offset, uint32_t who/*=UNKNOWN*/)
{
	offset &= 0xFFFFFF;

	// First 2M is mirrored in the $0 - $7FFFFF range
	if (offset < 0x800000)
	{
		return (jaguarMainRAM[(offset+0) & 0x1FFFFF] << 8) | jaguarMainRAM[(offset+1) & 0x1FFFFF];
	}
	else if ((offset >= 0x800000) && (offset < 0xDFFF00))
	{
		offset -= 0x800000;
		return (jaguarMainROM[offset+0] << 8) | jaguarMainROM[offset+1];
	}
	else if ((offset >= 0xDFFF00) && (offset <= 0xDFFFFE))
		return CDROMReadWord(offset, who);
	else if ((offset >= 0xE00000) && (offset <= 0xE3FFFE))
		return (jagMemSpace[offset + 0] << 8) | jagMemSpace[offset + 1];
	else if ((offset >= 0xF00000) && (offset <= 0xF0FFFE))
		return TOMReadWord(offset, who);
	else if ((offset >= 0xF10000) && (offset <= 0xF1FFFE))
		return JERRYReadWord(offset, who);

	return jaguar_unknown_readword(offset, who);
}


void JaguarWriteByte(uint32_t offset, uint8_t data, uint32_t who/*=UNKNOWN*/)
{
  offset &= 0xFFFFFF;

  // First 2M is mirrored in the $0 - $7FFFFF range
  if (offset < 0x800000)
    {
      jaguarMainRAM[offset & 0x1FFFFF] = data;
      return;
    }
  else if ((offset >= 0xDFFF00) && (offset <= 0xDFFFFF))
    {
      CDROMWriteByte(offset, data, who);
      return;
    }
  else if ((offset >= 0xF00000) && (offset <= 0xF0FFFF))
    {
      TOMWriteByte(offset, data, who);
      return;
    }
  else if ((offset >= 0xF10000) && (offset <= 0xF1FFFF))
    {
      JERRYWriteByte(offset, data, who);
      return;
    }
	
  jaguar_unknown_writebyte(offset, data, who);
}


uint32_t starCount;
void JaguarWriteWord(uint32_t offset, uint16_t data, uint32_t who/*=UNKNOWN*/)
{
  offset &= 0xFFFFFF;

  // First 2M is mirrored in the $0 - $7FFFFF range
  if (offset <= 0x7FFFFE)
    {
      /*
	GPU Table (CD BIOS)

	1A 69 F0 ($0000) -> Starfield
	1A 73 C8 ($0001) -> Final clearing blit & bitmap blit?
	1A 79 F0 ($0002)
	1A 88 C0 ($0003)
	1A 8F E8 ($0004) -> "Jaguar" small color logo?
	1A 95 20 ($0005)
	1A 9F 08 ($0006)
	1A A1 38 ($0007)
	1A AB 38 ($0008)
	1A B3 C8 ($0009)
	1A B9 C0 ($000A)
      */

      jaguarMainRAM[(offset+0) & 0x1FFFFF] = data >> 8;
      jaguarMainRAM[(offset+1) & 0x1FFFFF] = data & 0xFF;
      return;
    }
  else if (offset >= 0xDFFF00 && offset <= 0xDFFFFE)
    {
      CDROMWriteWord(offset, data, who);
      return;
    }
  else if (offset >= 0xF00000 && offset <= 0xF0FFFE)
    {
      TOMWriteWord(offset, data, who);
      return;
    }
  else if (offset >= 0xF10000 && offset <= 0xF1FFFE)
    {
      JERRYWriteWord(offset, data, who);
      return;
    }
  // Don't bomb on attempts to write to ROM
  else if (offset >= 0x800000 && offset <= 0xEFFFFF)
    return;

  jaguar_unknown_writeword(offset, data, who);
}


// We really should re-do this so that it does *real* 32-bit access... !!! FIX !!!
uint32_t JaguarReadLong(uint32_t offset, uint32_t who/*=UNKNOWN*/)
{
	return (JaguarReadWord(offset, who) << 16) | JaguarReadWord(offset+2, who);
}


// We really should re-do this so that it does *real* 32-bit access... !!! FIX !!!
void JaguarWriteLong(uint32_t offset, uint32_t data, uint32_t who/*=UNKNOWN*/)
{
	JaguarWriteWord(offset, data >> 16, who);
	JaguarWriteWord(offset+2, data & 0xFFFF, who);
}


void JaguarSetScreenBuffer(uint32_t * buffer)
{
	// This is in TOM, but we set it here...
	screenBuffer = buffer;
}


void JaguarSetScreenPitch(uint32_t pitch)
{
	// This is in TOM, but we set it here...
	screenPitch = pitch;
}


//
// Jaguar console initialization
//
void JaguarInit(void)
{
  // For randomizing RAM
  srand(time(NULL));

  // Contents of local RAM are quasi-stable; we simulate this by randomizing RAM contents
  for(uint32_t i=0; i<0x200000; i+=4)
    *((uint32_t *)(&jaguarMainRAM[i])) = rand();

#ifdef CPU_DEBUG_MEMORY
  memset(readMem, 0x00, 0x400000);
  memset(writeMemMin, 0xFF, 0x400000);
  memset(writeMemMax, 0x00, 0x400000);
#endif
  lowerField = false;							// Reset the lower field flag
  //temp, for crappy crap that sux
  memset(jaguarMainRAM + 0x804, 0xFF, 4);

  m68k_pulse_reset();							// Need to do this so UAE disasm doesn't segfault on exit
  GPUInit();
  DSPInit();
  TOMInit();
  JERRYInit();
  CDROMInit();
}


//New timer based code stuffola...
void HalflineCallback(void);
void RenderCallback(void);
void JaguarReset(void)
{
  // Only problem with this approach: It wipes out RAM loaded files...!
  // Contents of local RAM are quasi-stable; we simulate this by randomizing RAM contents
  for(uint32_t i=8; i<0x200000; i+=4)
    *((uint32_t *)(&jaguarMainRAM[i])) = rand();

  // New timer base code stuffola...
  InitializeEventList();
  //Need to change this so it uses the single RAM space and load the BIOS
  //into it somewhere...
  //Also, have to change this here and in JaguarReadXX() currently
  // Only use the system BIOS if it's available...! (it's always available now!)
  // AND only if a jaguar cartridge has been inserted.
  if (vjs.useJaguarBIOS && jaguarCartInserted && !vjs.hardwareTypeAlpine)
    memcpy(jaguarMainRAM, jagMemSpace + 0xE00000, 8);
  else
    SET32(jaguarMainRAM, 4, jaguarRunAddress);

  //	WriteLog("jaguar_reset():\n");
  TOMReset();
  JERRYReset();
  GPUReset();
  DSPReset();
  CDROMReset();
  m68k_pulse_reset();								// Reset the 68000
  WriteLog("Jaguar: 68K reset. PC=%06X SP=%08X\n", m68k_get_reg(NULL, M68K_REG_PC), m68k_get_reg(NULL, M68K_REG_A7));

  lowerField = false;								// Reset the lower field flag
  //	SetCallbackTime(ScanlineCallback, 63.5555);
  //	SetCallbackTime(ScanlineCallback, 31.77775);
  SetCallbackTime(HalflineCallback, (vjs.hardwareTypeNTSC ? 31.777777777 : 32.0));
}


void JaguarDone(void)
{
	int32_t topOfStack = m68k_get_reg(NULL, M68K_REG_A7);
	WriteLog("M68K: Top of stack: %08X -> (%08X). Stack trace:\n", topOfStack, JaguarReadLong(topOfStack));
#if 0
	for(int i=-2; i<9; i++)
		WriteLog("%06X: %08X\n", topOfStack + (i * 4), JaguarReadLong(topOfStack + (i * 4)));
#else
	uint32_t address = topOfStack - (4 * 4 * 3);

	for(int i=0; i<10; i++)
	{
		WriteLog("%06X:", address);

		for(int j=0; j<4; j++)
		{
			WriteLog(" %08X", JaguarReadLong(address));
			address += 4;
		}

		WriteLog("\n");
	}
#endif

//	WriteLog("Jaguar: CD BIOS version %04X\n", JaguarReadWord(0x3004));
	WriteLog("Jaguar: Interrupt enable = $%02X\n", TOMReadByte(0xF000E1, JAGUAR) & 0x1F);
	WriteLog("Jaguar: Video interrupt is %s (line=%u)\n", ((TOMIRQEnabled(IRQ_VIDEO))
		&& (JaguarInterruptHandlerIsValid(64))) ? "enabled" : "disabled", TOMReadWord(0xF0004E, JAGUAR));
	M68K_show_context();

	CDROMDone();
	GPUDone();
	DSPDone();
	TOMDone();
	JERRYDone();
}


// Temp debugging stuff

void DumpMainMemory(void)
{
	FILE * fp = fopen("./memdump.bin", "wb");

	if (fp == NULL)
		return;

	fwrite(jaguarMainRAM, 1, 0x200000, fp);
	fclose(fp);
}


uint8_t * GetRamPtr(void)
{
	return jaguarMainRAM;
}


//
// New Jaguar execution stack
// This executes 1 frame's worth of code.
//
bool frameDone;
void JaguarExecuteNew(void)
{
	frameDone = false;

	do
	{
		double timeToNextEvent = GetTimeToNextEvent();
//WriteLog("JEN: Time to next event (%u) is %f usec (%u RISC cycles)...\n", nextEvent, timeToNextEvent, USEC_TO_RISC_CYCLES(timeToNextEvent));

		m68k_execute(USEC_TO_M68K_CYCLES(timeToNextEvent));

		if (vjs.GPUEnabled)
			GPUExec(USEC_TO_RISC_CYCLES(timeToNextEvent));

		HandleNextEvent();
 	}
	while (!frameDone);
}


//
// The thing to keep in mind is that the VC is advanced every HALF line,
// regardless of whether the display is interlaced or not. The only difference
// with an interlaced display is that the high bit of VC will be set when the
// lower field is being rendered. (NB: The high bit of VC is ALWAYS set on the
// lower field, regardless of whether it's in interlace mode or not.
// NB2: Seems it doesn't always, not sure what the constraint is...)
//
// Normally, TVs will render a full frame in 1/30s (NTSC) or 1/25s (PAL) by
// rendering two fields that are slighty vertically offset from each other.
// Each field is created in 1/60s (NTSC) or 1/50s (PAL), and every other line
// is rendered in this mode so that each field, when overlaid on each other,
// will yield the final picture at the full resolution for the full frame.
//
// We execute a half frame in each timeslice (1/60s NTSC, 1/50s PAL).
// Since the number of lines in a FULL frame is 525 for NTSC, 625 for PAL,
// it will be half this number for a half frame. BUT, since we're counting
// HALF lines, we double this number and we're back at 525 for NTSC, 625 for
// PAL.
//
// Scanline times are 63.5555... μs in NTSC and 64 μs in PAL
// Half line times are, naturally, half of this. :-P
//
void HalflineCallback(void)
{
	uint16_t vc = TOMReadWord(0xF00006, JAGUAR);
	uint16_t vp = TOMReadWord(0xF0003E, JAGUAR) + 1;
	uint16_t vi = TOMReadWord(0xF0004E, JAGUAR);
//	uint16_t vbb = TOMReadWord(0xF00040, JAGUAR);
	vc++;

	// Each # of lines is for a full frame == 1/30s (NTSC), 1/25s (PAL).
	// So we cut the number of half-lines in a frame in half. :-P
	uint16_t numHalfLines = ((vjs.hardwareTypeNTSC ? 525 : 625) * 2) / 2;

	if ((vc & 0x7FF) >= numHalfLines)
	{
		lowerField = !lowerField;
		// If we're rendering the lower field, set the high bit (#11, counting
		// from 0) of VC
		vc = (lowerField ? 0x0800 : 0x0000);
	}

//WriteLog("HLC: Currently on line %u (VP=%u)...\n", vc, vp);
	TOMWriteWord(0xF00006, vc, JAGUAR);

	// Time for Vertical Interrupt?
	if ((vc & 0x7FF) == vi && (vc & 0x7FF) > 0 && TOMIRQEnabled(IRQ_VIDEO))
	{
		// We don't have to worry about autovectors & whatnot because the Jaguar
		// tells you through its HW registers who sent the interrupt...
		TOMSetPendingVideoInt();
		m68k_set_irq(2);
	}

	TOMExecHalfline(vc, true);

//Change this to VBB???
//Doesn't seem to matter (at least for Flip Out & I-War)
	if ((vc & 0x7FF) == 0)
//	if (vc == vbb)
	{
		JoystickExec();
		frameDone = true;
	}//*/

	SetCallbackTime(HalflineCallback, (vjs.hardwareTypeNTSC ? 31.777777777 : 32.0));
}

