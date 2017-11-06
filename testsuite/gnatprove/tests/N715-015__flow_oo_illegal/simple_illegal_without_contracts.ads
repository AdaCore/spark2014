 package Simple_Illegal_Without_Contracts is pragma Elaborate_Body;
   type Level_0_T (D : Integer) is tagged record
      A : Integer;
      case D is
         when 0 =>
            Extra : Integer;

         when others =>
            null;
      end case;
   end record;

   PI, I , IO, O : Integer := 0;

   procedure P (Par : in out Level_0_T);

   type Level_1_1_T is new Level_0_T with record
      B1 : Integer;
   end record;

   procedure P (Par : in out Level_1_1_T);

   type Level_1_2_T is new Level_0_T with record
      B2 : Integer;
   end record;

   procedure P (Par : in out Level_1_2_T);

   type Level_1_3_T is new Level_0_T with record
      B3 : Integer;
   end record;

   procedure P (Par : in out Level_1_3_T);

   type Level_1_T is new Level_0_T with record
      B : Integer;
   end record;

   procedure P (Par : in out Level_1_T);

   type Level_2_1_T is new Level_1_T with record
      C1 : Integer;
   end record;

   procedure P (Par : in out Level_2_1_T);
end Simple_Illegal_Without_Contracts;
