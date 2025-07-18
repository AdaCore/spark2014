package body Test_Protected is

   protected body Prot is
      function Get return Integer is (X);

      procedure Set (I : Integer) is
      begin
         X := I;
      end Set;

      procedure Do_Nothing (I : Integer) is
      begin
         null;
      end Do_Nothing;

      --  Both Set_2 and Do_Nothing_2 are considered to have the self reference
      --  as an implicit in out parameter even if they are not protected
      --  operations.

      procedure Set_2 (I : Integer) with
        Program_Exit => Get = I;
      procedure Set_2 (I : Integer) is
      begin
         X := I;
      end Set_2;

      procedure Do_Nothing_2 (I : Integer) with
        Program_Exit => Get = I;
      procedure Do_Nothing_2 (I : Integer) is
      begin
         null;
      end Do_Nothing_2;

      procedure Nested is

         --  For nested subprograms, the implicit parameter is scoped. Therefore
         --  it is handled as a Global with its own mode and Do_Nothing_3 is
         --  recognized as not modifying it.

         procedure Set_3 (I : Integer) with
           Program_Exit => Get = I;
         procedure Set_3 (I : Integer) is
         begin
            X := I;
         end Set_3;

         procedure Do_Nothing_3 (I : Integer) with
           Program_Exit => Get = I;
         procedure Do_Nothing_3 (I : Integer) is
         begin
            null;
         end Do_Nothing_3;
      begin
         Do_Nothing_3 (0);
         Set_3 (0);
      end Nested;

   end Prot;

end Test_Protected;
