with P2;

package P5 is

   type Index is new Integer range 1 .. 3;

   type Array_of_Limited_Records is array (Index) of P2.Limited_Record;

end;
