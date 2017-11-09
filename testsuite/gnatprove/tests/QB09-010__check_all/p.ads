with Get;
with Broken;

package P is

   X : constant Boolean := Get;
   --  Generated global of Get is needed to decide whether X has variable
   --  input, but Broken contains compilation errors. Then gnatprove goes into
   --  phase 2 without get.ali and broken.ali, and then crashes.

end P;
