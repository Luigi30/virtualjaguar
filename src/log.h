//
// log.h: Logfile support
//

#ifndef __LOG_H__
#define __LOG_H__

#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

  int LogInit(const char *);
  FILE * LogGet(void);
  void LogDone(void);
  void WriteLog(const char * text, ...);

  int FakeSkunkLogInit(const char *);
  void FakeSkunkLogByte(const unsigned char c);
  
#ifdef __cplusplus
}
#endif

// Some useful defines... :-)
//#define GPU_DEBUG
//#define LOG_BLITS

#endif	// __LOG_H__
