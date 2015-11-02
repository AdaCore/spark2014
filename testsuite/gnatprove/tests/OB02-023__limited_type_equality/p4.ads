with P1;

package P4 is

   type Index is new Integer range 1 .. 3;

   type Array_of_Normal_Records is array (Index) of P1.Normal_Record;

end;
