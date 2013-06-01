with Unc; use Unc;
  
package Unc_Test is

  procedure Linear_Search
    (Table : in Vector;
     Value : in Integer;
     Found : out Boolean;
     Index : out Integer);
  pragma Postcondition (not Found or else Table(Index) = Value);

  function Check_Index
    (Table : Vector;
     Value : Integer;
     Index : Integer) return Boolean;
  pragma Precondition (Table'First <= Index and then Index <= Table'Last);
  pragma Postcondition (Check_Index'Result = (Table(Index) = Value));

end Unc_Test;
