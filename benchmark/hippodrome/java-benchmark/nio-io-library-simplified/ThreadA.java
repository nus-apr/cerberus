package com.test;

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import com.facebook.infer.annotation.ThreadSafe;

@ThreadSafe
public class ThreadA {

	byte[] messageByte = new byte[100];

	public void foo(boolean read) {
		  ServerSocket server;
		  Socket clientSocket = null;
		  int currentBytesRead;

		  try {
		  server = new ServerSocket(8080);
		  Socket socket = server.accept();

		  DataInputStream in = new DataInputStream(new BufferedInputStream(socket.getInputStream()));
		  DataOutputStream out = new DataOutputStream(clientSocket.getOutputStream());
		  
		  if(read) 
			  currentBytesRead = in.read(messageByte);
		  else
			  out.write(messageByte);
		  } catch (IOException e) {
		  e.printStackTrace(); }
	}
}