package Test is
   type Record_T is record
      X : Integer;
   end Record;

   function Equivalent (A, B : Record_T) return Boolean;

   function "=" (Left, Right : Record_T) return Boolean renames Equivalent;
end Test;
