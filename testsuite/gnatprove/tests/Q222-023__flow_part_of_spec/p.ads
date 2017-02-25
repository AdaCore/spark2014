package P with SPARK_Mode, Abstract_State => State is

   function Expose return Integer with Global => (Input => State);

private

   Secret : Integer := 0 with Part_Of => State;

end;
