package A with
  SPARK_Mode,
  Abstract_State => (aDATA1)
is
   pragma Elaborate_Body (A);
private
   DATA1 : Integer := 0 with Part_Of => aDATA1;
end A;
