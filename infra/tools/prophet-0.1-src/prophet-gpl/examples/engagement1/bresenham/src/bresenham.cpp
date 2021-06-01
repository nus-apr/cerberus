/* original courtesy of player1537, http://www.cemetech.net/forum/viewtopic.php?t=5401 */

#include <stdlib.h>
#include <stdio.h>

#include "Bresenham.h"

  void buggy(unsigned x1, unsigned y1,
			    DiscreteLine & line)
  {
    short x0 = 0, y0 = 0;

    bool steep = abs(y1 - y0) > abs(x1 - x0);
    short a;
     if (steep)
       {
	 a = x0; x0 = y0; y0 = a;
	 a = x1; x1 = y1; y1 = a;
       }
     if (x0 > x1)
       {
	 a = x0; x0 = x1; x1 = a;
	 a = y0; y0 = y1; y1 = a;
       }

     int deltax = x1 - x0;
     int deltay = abs(y1 - y0);
     float error = 0;
     float deltaerr = deltay / deltax;
     int ystep;
     if (y0 < y1)
       ystep = 1;
     else
       ystep = -1;

     int y = y0;
     for (int x = x0;x < x1;x++)
       {
	 if (steep)
	   line.push_back(std::make_pair(y,x));
	 else
	   line.push_back(std::make_pair(x,y));
	 error = error + deltaerr;
	 if (error >= 0.5)
	   {
	     y += ystep;
	     error = error - 1;
	   }
       }
  }

int main(int argc, char **argv)
{
  FILE *f = fopen(argv[1], "r");
  int x, y;
  fscanf(f, "%d %d\n", &x, &y);
  fclose(f);
  DiscreteLine line;
  buggy(x, y, line);

  for (unsigned i = 0, end = line.size(); i != line.size(); i++)
    printf("%d %d\n", line[i].first, line[i].second);
}
