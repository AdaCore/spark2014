with System.Storage_Elements;

package Volatiles_Legal
  with SPARK_Mode
is
   --  TU: 7. Every update of an external state is considered to be read by
   --  some external reader if Async_Readers => True.

   --  TU: 8. Each successive read of an external state might have a different
   --  value [written by some external writer] if Async_Writers => True.

   --  TU: 9. If Effective_Writes => True, then every value written to the
   --  external state is significant. [For instance writing a sequence
   --  of values to a port.]

   --  TU: 10. If Effective_Reads => True, then every value read from the
   --  external state is significant. [For example a value read from a
   --  port might be used in determining how the next value is
   --  processed.]

   --  TU: 11. Each update of an external state has no external effect if both
   --  Async_Readers => False and Effective_Writes => False.

   --  TU: 12. Each successive read of an external state will result in the
   --  last value explicitly written [by the program] if Async_Writers =>
   --  False.

   --  TU: 13. Every explicit update of an external state might affect the next
   --  value read from the external state even if Async_Writers => True.

   --  TU: 14. An external state which has the property Async_Readers => True
   --  need not be initialized before being read although explicit
   --  initialization is permitted. [The external state might be
   --  initialized by an external writer.]

   type Vol_Rec_T is record
      X : Integer;
   end record with Volatile;

   Vol : Vol_Rec_T
     with Async_Readers,
          Async_Writers => False,
          Address => System.Storage_Elements.To_Address (16#BA12#);

   Vol2 : Vol_Rec_T
     with Async_Writers,
          Address => System.Storage_Elements.To_Address (16#BABE5#);

   procedure P1 (Par : in out Vol_Rec_T);

   procedure P2
     with Global => (In_Out => Vol);

   procedure P3
     with Global => (Output => Vol2);
end Volatiles_Legal;
