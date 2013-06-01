package body Sub is
   function Remove_Absent (X : Ext_Dir) return Dir is
   begin
      case X is
         when Absent | Left =>
            return Left;
         when Right =>
            return Right;
      end case;
   end Remove_Absent;

   function Remove_Absent (X : Ext_Dir) return Dir2 is
   begin
      case X is
         when Absent | Left =>
            return Left;
         when Right =>
            return Right;
      end case;
   end Remove_Absent;

   procedure P is
      X : Dir := Left;
      Y : Ext_Dir := X;
      Z : Dir := Y;
   begin
      null;
   end P;

   procedure P (X : Dir) is
      Y : Ext_Dir := X;
      Z : Dir := Y;
   begin
      null;
   end P;
end Sub;
