with Update;

procedure Main (Some_Condition : Boolean; Status : out Integer) is
begin
   Main_Block : for Unused_Loop_Var in 1 .. 1 loop
      pragma Unreferenced (Unused_Loop_Var);

      if Some_Condition then
         Status := 1;
         exit Main_Block;
      end if;

      Update (Status);

      exit Main_Block when Status /= 0;

      return;

   end loop Main_Block;

   -- Dead code forced by super strong "out" semantics
   pragma Assert(Status /= 0);

   Update (Status);
end Main;
