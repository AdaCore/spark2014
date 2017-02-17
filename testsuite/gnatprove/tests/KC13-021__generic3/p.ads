generic
   X : in out Integer;
   Y : in out Integer;
package P is

   procedure Proc;
   pragma Postcondition (Y = X'Old);

end;

