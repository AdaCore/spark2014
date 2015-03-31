package Stack_05
--# own S, Pointer;     -- concrete state
--# initializes S, Pointer;
is
   procedure Push(X : in Integer);
   --# global in out S, Pointer;

   procedure Pop(X : out Integer);
   --# global in S; in out Pointer;
end Stack_05;
