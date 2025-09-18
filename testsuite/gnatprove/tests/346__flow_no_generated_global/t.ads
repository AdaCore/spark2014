package T with Abstract_State => State is
   function I return Integer with Global => State, Import;
   procedure Dummy;
end;
