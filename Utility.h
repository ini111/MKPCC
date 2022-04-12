/*
 *  Utility.h
 *
 *  Created on: 5Dec.,2017
 *      Author: Lijun Chang
 *      Email: ljchang@outlook.com
 * 	modified Yi Zhou 2019-12-8
 *  modified-V2 Zhengren Wang 2021-11-14
 */

#ifndef UTILITY_H_
#define UTILITY_H_
#pragma warning(disable : 4996)
#include <string>
#include <vector>
#include <time.h>
#include "Defines.h"

class Utility {
public:
	/*static int fileSuffixPos(const char* filepath) {
		int j = strlen(filepath) - 1;
		while (filepath[j] != '.')
			j--;
		return j + 1;
	}
	*/

	static FILE *open_file(const char *file_name, const char *mode) {
		FILE *f = fopen(file_name, mode);
		if(f == nullptr) {
			printf("Can not open file: %s\n", file_name);
			exit(1);
		}

		return f;
	}

	static std::string integer_to_string(long long number) {
		std::vector<int> sequence;
		if(number == 0) sequence.push_back(0);
		while(number > 0) {
			sequence.push_back(number%1000);
			number /= 1000;
		}

		char buf[5];
		std::string res;
		for(unsigned int i = sequence.size();i > 0;i --) {
			if(i == sequence.size()) sprintf(buf, "%u", sequence[i-1]);
			else sprintf(buf, ",%03u", sequence[i-1]);
			res += std::string(buf);
		}
		return res;
	}

	static double elapse_seconds(clock_t st, clock_t end) {
		return (double)(end - st) / CLOCKS_PER_SEC;
	}
	
	//Prerequisite: lst1 and lst2 are sorted incrementally.
	static int countIntersect(int *lst1, int sz1, int *lst2, int sz2){
		if (sz1 ==0 || sz2 == 0) return 0;
		int p1=0, p2=0;
		int cnt = 0;
		while (p1 < sz1 && p2 <sz2){
			if (lst1[p1] == lst2[p2]){
				p1++;p2++; cnt++;
			}else if(lst1[p1] < lst2[p2])
				p1++;
			else p2++;
		}
		return cnt;
	}
};

#endif /* UTILITY_H_ */
