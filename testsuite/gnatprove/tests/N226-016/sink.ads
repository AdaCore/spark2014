with System;

package Sink
is
	The_Sink : Integer
		with Async_Readers, Effective_Writes, Volatile, Address => System'To_Address (16#1234#);
end Sink;
