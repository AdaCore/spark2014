package Abstract_State_Illegal
  with SPARK_Mode
is
   package Invalid_Parameters
     --  TU: ::
     --  abstract_state_list ::= null
     --             | state_name_with_options
     --             | ( state_name_with_options { , state_name_with_options } )
     --  state_name_with_options  ::= state_name
     --                             | ( state_name with option_list )
     --  option_list              ::= option { , option }
     --  option                   ::= simple_option
     --                             | name_value_option
     --  simple_option            ::= identifier
     --  name_value_option        ::= Part_Of => abstract_state
     --                             | External [=> external_property_list]
     --  external_property_list   ::= external_property
     --                           | ( external_property {, external_property} )
     --  external_property        ::= Async_Readers [=> expression]
     --                             | Async_Writers [=> expression]
     --                             | Effective_Writes [=> expression]
     --                             | Effective_Reads  [=> expression]
     --                             | others => expression
     --  state_name               ::= defining_identifier
     --  abstract_state           ::= name
     --  Currently no ``simple_options`` are defined.

     --  TU: 1. An ``option`` shall not be repeated within a single
     --  ``option_list``.

     --  TU: 2. If External is specified in an ``option_list`` then there shall
     --  be at most one occurrence of each of Async_Readers, Async_Writers,
     --  Effective_Writes and Effective_Reads.
     with Abstract_State => (S1,

                             (S2 + S3),  --  incorrect expression

                             S1,  --  same state_name appears twice

                             (S4 with Something),
                             --  Something is not a valid simple_option

                             (S5 with External => "bla"),
                             --  "bla" is not a valid external state property

                             (S6, S7),  --  Incorrectly placed parentheses

                             (S8 with External => (Async_Readers,
                                                   Async_Readers)),
                             --  property_list contains two occurrences of
                             --  Async_Readers.

                             null)  --  null is not the only state_name
   is
      function Increase(X : Integer; Y : Integer := 1) return Integer
        with Abstract_State => (One_Parameter, Another_Parameter, Input);
      --  incorrect placement of Abstract_State
   end Invalid_Parameters;


   package Null_Abstract_State_With_Hidden_State
     --  TU: 7. A **null** ``abstract_state_list`` specifies that a package
     --  contains no hidden state.
     with Abstract_State => null
   is
   private
      Priv_Var : Integer;
   end Null_Abstract_State_With_Hidden_State;


   package State_Same_As_Var
     --  TU: 5. A function declaration that overloads a state abstraction has
     --  an implicit Global aspect denoting the state abstraction with a
     --  ``mode_selector`` of Input. An explicit Global aspect may be specified
     --  which replaces the implicit one.
     with Abstract_State => S1  --  state_name conflicts with variable
   is
      S1 : Integer;
   end State_Same_AS_Var;
end Abstract_State_Illegal;
