procedure Test with SPARK_Mode => On is
  package Nested is
      type T is private with
        Aggregate => (Empty => Empty, Add_Unnamed => Add_Unnamed);

      function Empty return T;
      procedure Add_Unnamed (X : in out T; E : Boolean);
   private
      type T is record
         True_Present  : Boolean;
         False_Present : Boolean;
      end record;
   end Nested;

  package body Nested is
      function Empty return T is
      begin
         return R : T do
            R.True_Present := False;
            R.False_Present := False;
         end return;
      end Empty;
      procedure Add_Unnamed (X : in out T; E : Boolean) is
      begin
         if E then
            X.True_Present := True;
         else
            X.True_Present := False;
         end if;
      end Add_Unnamed;
   end Nested;
   use Nested;

   S : T := [True, False];
begin
   null;
end Test;
