package P is

   X : Boolean := True;

   function Id (Arg : Integer) return Integer is (Arg)
   with Pre     => X,
        Depends => (Id'Result => Arg, null => X);

   --  Those Globals are wrong
   function Wrapper1 (Arg : Integer) return Integer is (Id (Arg)) with Global => null;        -- crashes proof
   function Wrapper2 (Arg : Integer) return Integer is (Id (Arg)) with Global => (Input => X);

   --  Those Global/Depends are OK
   function Wrapper3 (Arg : Integer) return Integer is (Id (Arg)) with Global  => (Proof_In => X);
   function Wrapper4 (Arg : Integer) return Integer is (Id (Arg)) with Depends => (Wrapper4'Result => Arg, null => X);
end;
