with Arr; use Arr;

package Arr_Test is

  procedure Linear_Search
    (T     : Arr.Table;
     Value : Integer;
     Found : out Boolean;
     N     : out Arr.Index);
  pragma Postcondition (not Found or else T (N) = Value);

  function Check_Index
    (T     : Arr.Table;
     Value : Integer;
     N     : Arr.Index) return Boolean;
  pragma Precondition (T'First <= N and then N <= T'Last);
  pragma Postcondition (Check_Index'Result = (T (N) = Value));

end Arr_Test;
