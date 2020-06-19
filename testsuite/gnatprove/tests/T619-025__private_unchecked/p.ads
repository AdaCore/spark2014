with Ada.Unchecked_Conversion;

package P is

   type AST_Handler is private;

   type Unsigned_Longword is range -2_147_483_648 .. 2_147_483_647;

private

   --  An AST_Handler value is from a typing point of view simply a pointer
   --  to a procedure taking a single 64 bit parameter. However, this
   --  is a bit misleading, because the data that this pointer references is
   --  highly stylized. See body of System.AST_Handling for full details.

   type AST_Handler is access procedure (Param : Long_Integer);

   function To_Unsigned_Longword_A is new
     Ada.Unchecked_Conversion (AST_Handler, Unsigned_Longword);

end;
