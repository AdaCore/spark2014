procedure Main with SPARK_Mode is

   package Visible_By_Default is

      function My_And (X, Y : Boolean) return Boolean is (X and Y);

      function Use_And (X, Y : Boolean) return Boolean is (My_And (X, Y)) with
        Post => Use_And'Result = (X and Y); -- @POSTCONDITION:FAIL
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", My_And);

      function Use_And_2 (X, Y : Boolean) return Boolean is (My_And (X, Y)) with
        Post => Use_And_2'Result = (X and Y); -- @POSTCONDITION:PASS

      function Use_And_3 (X, Y : Boolean) return Boolean with
        Post => Use_And_3'Result = (X and Y); -- @POSTCONDITION:FAIL

   end Visible_By_Default;

   package body Visible_By_Default is

      function Use_And_3 (X, Y : Boolean) return Boolean is
         pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", My_And);
      begin
         return My_And (X, Y);
      end Use_And_3;

   end Visible_By_Default;

   package Hidden_By_Default is

      function My_And (X, Y : Boolean) return Boolean is (X and Y) with
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      function Use_And (X, Y : Boolean) return Boolean is (My_And (X, Y)) with
        Post => Use_And'Result = (X and Y); -- @POSTCONDITION:FAIL

      function Use_And_2 (X, Y : Boolean) return Boolean is (My_And (X, Y)) with
        Post => Use_And_2'Result = (X and Y); -- @POSTCONDITION:PASS
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", My_And);

      function Use_And_3 (X, Y : Boolean) return Boolean with
        Post => Use_And_3'Result = (X and Y); -- @POSTCONDITION:PASS

   end Hidden_By_Default;

   package body Hidden_By_Default is

      function Use_And_3 (X, Y : Boolean) return Boolean is
         pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", My_And);
      begin
         return My_And (X, Y);
      end Use_And_3;

   end Hidden_By_Default;

   package Recursive is

      --  Rec_And is hidden for its recursive calls too

      function Rec_And (X, Y : Boolean) return Boolean is
        (if not X then False elsif X = Y then True else Rec_And (Y, X))
          with
            Subprogram_Variant => (Decreases => X),
            Post => (if X then Rec_And'Result = Y), -- @POSTCONDITION:FAIL
            Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

      --  The second annotation overrides the default for recursive calls

      function Rec_And_2 (X, Y : Boolean) return Boolean is
        (if not X then False elsif X = Y then True else Rec_And_2 (Y, X))
          with
            Subprogram_Variant => (Decreases => X),
            Post => (if X then Rec_And_2'Result = Y), -- @POSTCONDITION:PASS
            Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
            Annotate => (GNATprove, Unhide_Info, "Expression_Function_Body");

      --  But not for external calls

      function Use_Rec_And_2 (X, Y : Boolean) return Boolean is (Rec_And_2 (X, Y)) with
        Post => Use_Rec_And_2'Result = (X and Y); -- @POSTCONDITION:FAIL

   end Recursive;

begin
   null;
end Main;
