with System.Storage_Elements;
with Volatiles_Illegal_Helper;

package Volatiles_Illegal_2
  --  TU: 3. A property may be explicitly given the value False [for instance
  --  Async_Readers => False].

  --  TU: 5. The expression defining the Boolean valued property shall be
  --  static.

  --  TU: 6. Only the following combinations of properties are valid:
  --  * Async_Readers, Effective_Writes, others => False;
  --  * Async_Writers, Effective_Reads, others => False;
  --  * Async_Readers, others => False;
  --  * Async_Writers, others => False;
  --  * Async_Readers, Async_Writers, Effective_Writes, others => False;
  --  * Async_Readers, Async_Writers, Effective_Reads, others => False;
  --  * Async_Readers, Async_Writers, others => False; and
  --  * others => True.
  --    [Another way of expressing this rule is that Effective_Reads can
  --    only be True if Async_Writers is True and Effective_Writes can only
  --    be True if Async_Readers is True.]

  --  TU: 4. The aspects shall only be specified in the aspect specification of
  --  a Volatile object declaration excluding Volatile formal parameter
  --  declarations.
  with SPARK_Mode,
       Abstract_State => ((State with External => (others => False)),
                          --  The above should not be allowed.

                          (State2 with External =>
                             (Async_Readers => Volatiles_Illegal_Helper.F)),
                          --  Expression is not static.

                          (State3 with External => (Async_Readers,
                                                    Effective_Reads)),
                          --  Not a valid combination of options.

                          (State4 with External => (Async_Readers => False,
                                                    others => True)))
                          --  Another invalid combination of options.
is
   X : Integer
     with Async_Writers,
          Address => System.Storage_Elements.To_Address (16#B01D0#);
   --  Cannot have property Async_Writers on a non-Volatile.

   procedure Proc (X : Integer with Volatile, Async_Readers);
   --  Formal parameter declarations cannot have Volatile and/or
   --  Async_Readers.
end Volatiles_Illegal_2;
