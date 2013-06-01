with Two; use Two;

package Two_Test is

  procedure Linear_Search
    (T     : Two.Table;
     Value : Integer;
     Found : out Boolean;
     I1    : out Two.Index;
     I2    : out Two.Index);
  pragma Postcondition (not Found or else T (I1, I2) = Value);

  function Check_Index
    (T     : Two.Table;
     Value : Integer;
     I1    : Two.Index;
     I2    : Two.Index) return Boolean;
  pragma Precondition (T'First (1) <= I1
		       and then I1 <= T'Last
		       and then T'First (2) <= I2
		       and then I2 <= T'Last (2));
  pragma Postcondition (Check_Index'Result = (T (I1, I2) = Value));

end Two_Test;
