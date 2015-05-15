package Triangle is

   function Sum_Up_To (N : Natural) return Natural
   with Pre => N <= 10000,
        Post =>
         Sum_Up_To'Result = N * (N + 1) / 2;
end Triangle;
