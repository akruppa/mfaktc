/*
This file is part of mfaktc.
Copyright (C) 2009, 2010, 2011  Oliver Weihe (o.weihe@t-online.de)

mfaktc is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

mfaktc is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
                                
You should have received a copy of the GNU General Public License
along with mfaktc.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef _TIMER_H
#define _TIMER_H 1

#ifndef _MSC_VER
#include <sys/time.h>
#else
#include "timeval.h"
#endif

#if defined(NVCC_EXTERN) && !defined(_MSC_VER)
extern "C" {
#endif
void timer_init(struct timeval *timer);
unsigned long long int timer_diff(struct timeval *timer);
void timertest();
void sleeptest();
int sleep_is_good();
#if defined(NVCC_EXTERN) && !defined(_MSC_VER)
}
#endif

#endif /* _TIMER_H */
