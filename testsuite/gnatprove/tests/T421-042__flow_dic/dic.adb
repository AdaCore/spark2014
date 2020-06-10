procedure DIC is
   X : Boolean;  --  intentionally uninitialized and then mentioned in DIC
   package P is
      type T is private with Default_Initial_Condition => Is_Zero (T) and X;
      function Zero return T;
      function Is_Zero (Arg : T) return Boolean;
   private
      type T is new Integer with Default_Value => 0;
      function Zero return T is (0);
      function Is_Zero (Arg : T) return Boolean is (Arg = 0);
   end;

   Y : P.T := P.Zero;   --  DIC is *not* evaluated here
   Z : P.T with Import; --  DIC is *not* evaluated here
begin
   pragma Assert (P.Is_Zero (Y));
end;
