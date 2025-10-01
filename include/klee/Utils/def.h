//
// Created by yuhao on 3/7/23.
//

#ifndef KLEE_DEF_H
#define KLEE_DEF_H

#define LOG_LEVEL (0)
#define LOG_FILE (1)
#define LOG_TIME (1)
#define LOG_COLOR (0)

/// Different colors for output
#define LOG_NRM "\x1B[0m "  /* Normal */
#define LOG_RED "\x1B[31m " /* Red */
#define LOG_GRN "\x1B[32m " /* Green */
#define LOG_YEL "\x1B[33m " /* Yellow */
#define LOG_BLU "\x1B[34m " /* Blue */
#define LOG_MAG "\x1B[35m " /* Magenta */
#define LOG_CYN "\x1B[36m " /* Cyan */
#define LOG_WHT "\x1B[37m " /* White */

#define DELIMITER '$'
#define Annotation_Symbol "# "

#define ENTRYPOINT "entry-point"
#define MODULES "modules"

#endif // KLEE_DEF_H
