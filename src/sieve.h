/*
This file is part of mfaktc.
Copyright (C) 2009, 2010, 2011, 2013  Oliver Weihe (o.weihe@t-online.de)

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

int class_needed(unsigned int exp, unsigned long long int k_min, unsigned int c,
                 unsigned int num_classes, int verbosity);
void sieve_init();
void sieve_free();
void sieve_init_class(unsigned int exp, unsigned long long int k_start, int sieve_limit);
int sieve_euclid_modified(int j, int n, int r);

#if defined(NVCC_EXTERN) && !defined(_MSC_VER)
extern "C" {
#endif
void sieve_candidates(int ktab_size, unsigned int *ktab, int sieve_limit);
#if defined(NVCC_EXTERN) && !defined(_MSC_VER)
}
#endif
