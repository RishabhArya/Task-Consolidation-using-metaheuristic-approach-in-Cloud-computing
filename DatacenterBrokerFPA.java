/*
 * Title:        CloudSim Toolkit
 * Description:  CloudSim (Cloud Simulation) Toolkit for Modeling and Simulation of Clouds
 * Licence:      GPL - http://www.gnu.org/copyleft/gpl.html
 *
 * Copyright (c) 2009-2012, The University of Melbourne, Australia
 */

package org.cloudbus.cloudsim;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Scanner;

import org.cloudbus.cloudsim.core.CloudSim;
import org.cloudbus.cloudsim.core.CloudSimTags;
import org.cloudbus.cloudsim.core.SimEntity;
import org.cloudbus.cloudsim.core.SimEvent;
import org.cloudbus.cloudsim.lists.CloudletList;
import org.cloudbus.cloudsim.lists.VmList;

/**
 * DatacentreBroker represents a broker acting on behalf of a user. It hides VM management, as vm
 * creation, sumbission of cloudlets to this VMs and destruction of VMs.
 * 
 * @author Rodrigo N. Calheiros
 * @author Anton Beloglazov
 * @since CloudSim Toolkit 1.0
 */
public class DatacenterBroker extends SimEntity {

	/** The vm list. */
	protected List<? extends Vm> vmList;

	/** The vms created list. */
	protected List<? extends Vm> vmsCreatedList;

	/** The cloudlet list. */
	protected List<? extends Cloudlet> cloudletList;

	/** The cloudlet submitted list. */
	protected List<? extends Cloudlet> cloudletSubmittedList;

	/** The cloudlet received list. */
	protected List<? extends Cloudlet> cloudletReceivedList;

	/** The cloudlets submitted. */
	protected int cloudletsSubmitted;

	/** The vms requested. */
	protected int vmsRequested;

	/** The vms acks. */
	protected int vmsAcks;

	/** The vms destroyed. */
	protected int vmsDestroyed;

	/** The datacenter ids list. */
	protected List<Integer> datacenterIdsList;

	/** The datacenter requested ids list. */
	protected List<Integer> datacenterRequestedIdsList;

	/** The vms to datacenters map. */
	protected Map<Integer, Integer> vmsToDatacentersMap;

	/** The datacenter characteristics list. */
	protected Map<Integer, DatacenterCharacteristics> datacenterCharacteristicsList;

	/**
	 * Created a new DatacenterBroker object.
	 * 
	 * @param name name to be associated with this entity (as required by Sim_entity class from
	 *            simjava package)
	 * @throws Exception the exception
	 * @pre name != null
	 * @post $none
	 */
	
	//list to store initial population
	protected List<ArrayList<ArrayList<Integer>>> Population=new ArrayList<ArrayList<ArrayList<Integer>>>();
	//list to store best solution
	protected ArrayList<ArrayList<Integer>> bestSoln=new ArrayList<ArrayList<Integer>>();
	
	//no of initial solutions
	protected int solutioncount=20;
	//fitness of solutions in population
	protected double [][] fitness=new double[solutioncount][2];
	
	//to store new solution
	protected ArrayList<ArrayList<Integer>> newsol=new ArrayList<ArrayList<Integer>>();
	
	//to store vmexecution time of each vm in new solution
	protected double vmTimes[][];
	protected int avg;
	
	public DatacenterBroker(String name) throws Exception {
		super(name);

		setVmList(new ArrayList<Vm>());
		setVmsCreatedList(new ArrayList<Vm>());
		setCloudletList(new ArrayList<Cloudlet>());
		setCloudletSubmittedList(new ArrayList<Cloudlet>());
		setCloudletReceivedList(new ArrayList<Cloudlet>());

		cloudletsSubmitted = 0;
		setVmsRequested(0);
		setVmsAcks(0);
		setVmsDestroyed(0);

		setDatacenterIdsList(new LinkedList<Integer>());
		setDatacenterRequestedIdsList(new ArrayList<Integer>());
		setVmsToDatacentersMap(new HashMap<Integer, Integer>());
		setDatacenterCharacteristicsList(new HashMap<Integer, DatacenterCharacteristics>());
	}

	/**
	 * This method is used to send to the broker the list with virtual machines that must be
	 * created.
	 * 
	 * @param list the list
	 * @pre list !=null
	 * @post $none
	 */
	public void submitVmList(List<? extends Vm> list) {
		getVmList().addAll(list);
	}

	/**
	 * This method is used to send to the broker the list of cloudlets.
	 * 
	 * @param list the list
	 * @pre list !=null
	 * @post $none
	 */
	public void submitCloudletList(List<? extends Cloudlet> list) {
		getCloudletList().addAll(list);
	}

	/**
	 * Specifies that a given cloudlet must run in a specific virtual machine.
	 * 
	 * @param cloudletId ID of the cloudlet being bount to a vm
	 * @param vmId the vm id
	 * @pre cloudletId > 0
	 * @pre id > 0
	 * @post $none
	 */
	public void bindCloudletToVm(int cloudletId, int vmId) {
		CloudletList.getById(getCloudletList(), cloudletId).setVmId(vmId);
	}

	/**
	 * Processes events available for this Broker.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != null
	 * @post $none
	 */
	@Override
	public void processEvent(SimEvent ev) {
		switch (ev.getTag()) {
		// Resource characteristics request
			case CloudSimTags.RESOURCE_CHARACTERISTICS_REQUEST:
				processResourceCharacteristicsRequest(ev);
				break;
			// Resource characteristics answer
			case CloudSimTags.RESOURCE_CHARACTERISTICS:
				processResourceCharacteristics(ev);
				break;
			// VM Creation answer
			case CloudSimTags.VM_CREATE_ACK:
				processVmCreate(ev);
				break;
			// A finished cloudlet returned
			case CloudSimTags.CLOUDLET_RETURN:
				processCloudletReturn(ev);
				break;
			// if the simulation finishes
			case CloudSimTags.END_OF_SIMULATION:
				shutdownEntity();
				break;
			// other unknown tags are processed by this method
			default:
				processOtherEvent(ev);
				break;
		}
	}

	/**
	 * Process the return of a request for the characteristics of a PowerDatacenter.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != $null
	 * @post $none
	 */
	protected void processResourceCharacteristics(SimEvent ev) {
		DatacenterCharacteristics characteristics = (DatacenterCharacteristics) ev.getData();
		getDatacenterCharacteristicsList().put(characteristics.getId(), characteristics);

		if (getDatacenterCharacteristicsList().size() == getDatacenterIdsList().size()) {
			setDatacenterRequestedIdsList(new ArrayList<Integer>());
			createVmsInDatacenter(getDatacenterIdsList().get(0));
		}
	}

	/**
	 * Process a request for the characteristics of a PowerDatacenter.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != $null
	 * @post $none
	 */
	protected void processResourceCharacteristicsRequest(SimEvent ev) {
		setDatacenterIdsList(CloudSim.getCloudResourceList());
		setDatacenterCharacteristicsList(new HashMap<Integer, DatacenterCharacteristics>());

		Log.printLine(CloudSim.clock() + ": " + getName() + ": Cloud Resource List received with "
				+ getDatacenterIdsList().size() + " resource(s)");

		for (Integer datacenterId : getDatacenterIdsList()) {
			sendNow(datacenterId, CloudSimTags.RESOURCE_CHARACTERISTICS, getId());
		}
	}

	/**
	 * Process the ack received due to a request for VM creation.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != null
	 * @post $none
	 */
	protected void processVmCreate(SimEvent ev) {
		int[] data = (int[]) ev.getData();
		int datacenterId = data[0];
		int vmId = data[1];
		int result = data[2];

		if (result == CloudSimTags.TRUE) {
			getVmsToDatacentersMap().put(vmId, datacenterId);
			getVmsCreatedList().add(VmList.getById(getVmList(), vmId));
			Log.printLine(CloudSim.clock() + ": " + getName() + ": VM #" + vmId
					+ " has been created in Datacenter #" + datacenterId + ", Host #"
					+ VmList.getById(getVmsCreatedList(), vmId).getHost().getId());
		} else {
			Log.printLine(CloudSim.clock() + ": " + getName() + ": Creation of VM #" + vmId
					+ " failed in Datacenter #" + datacenterId);
		}

		incrementVmsAcks();

		// all the requested VMs have been created
		if (getVmsCreatedList().size() == getVmList().size() - getVmsDestroyed()) {
			submitCloudlets();
		} else {
			// all the acks received, but some VMs were not created
			if (getVmsRequested() == getVmsAcks()) {
				// find id of the next datacenter that has not been tried
				for (int nextDatacenterId : getDatacenterIdsList()) {
					if (!getDatacenterRequestedIdsList().contains(nextDatacenterId)) {
						createVmsInDatacenter(nextDatacenterId);
						return;
					}
				}

				// all datacenters already queried
				if (getVmsCreatedList().size() > 0) { // if some vm were created
					submitCloudlets();
				} else { // no vms created. abort
					Log.printLine(CloudSim.clock() + ": " + getName()
							+ ": none of the required VMs could be created. Aborting");
					finishExecution();
				}
			}
		}
	}

	/**
	 * Process a cloudlet return event.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != $null
	 * @post $none
	 */
	protected void processCloudletReturn(SimEvent ev) {
		Cloudlet cloudlet = (Cloudlet) ev.getData();
		getCloudletReceivedList().add(cloudlet);
		Log.printLine(CloudSim.clock() + ": " + getName() + ": Cloudlet " + cloudlet.getCloudletId()
				+ " received");
		cloudletsSubmitted--;
		if (getCloudletList().size() == 0 && cloudletsSubmitted == 0) { // all cloudlets executed
			Log.printLine(CloudSim.clock() + ": " + getName() + ": All Cloudlets executed. Finishing...");
			clearDatacenters();
			finishExecution();
		} else { // some cloudlets haven't finished yet
			if (getCloudletList().size() > 0 && cloudletsSubmitted == 0) {
				// all the cloudlets sent finished. It means that some bount
				// cloudlet is waiting its VM be created
				clearDatacenters();
				createVmsInDatacenter(0);
			}

		}
	}

	/**
	 * Overrides this method when making a new and different type of Broker. This method is called
	 * by {@link #body()} for incoming unknown tags.
	 * 
	 * @param ev a SimEvent object
	 * @pre ev != null
	 * @post $none
	 */
	protected void processOtherEvent(SimEvent ev) {
		if (ev == null) {
			Log.printLine(getName() + ".processOtherEvent(): " + "Error - an event is null.");
			return;
		}

		Log.printLine(getName() + ".processOtherEvent(): "
				+ "Error - event unknown by this DatacenterBroker.");
	}

	/**
	 * Create the virtual machines in a datacenter.
	 * 
	 * @param datacenterId Id of the chosen PowerDatacenter
	 * @pre $none
	 * @post $none
	 */
	protected void createVmsInDatacenter(int datacenterId) {
		// send as much vms as possible for this datacenter before trying the next one
		int requestedVms = 0;
		String datacenterName = CloudSim.getEntityName(datacenterId);
		for (Vm vm : getVmList()) {
			if (!getVmsToDatacentersMap().containsKey(vm.getId())) {
				Log.printLine(CloudSim.clock() + ": " + getName() + ": Trying to Create VM #" + vm.getId()
						+ " in " + datacenterName);
				sendNow(datacenterId, CloudSimTags.VM_CREATE_ACK, vm);
				requestedVms++;
			}
		}

		getDatacenterRequestedIdsList().add(datacenterId);

		setVmsRequested(requestedVms);
		setVmsAcks(0);
	}

	/**
	 * Submit cloudlets to the created VMs.
	 * 
	 * @pre $none
	 * @post $none
	 */
	/**
	 * 
	 */
//	protected void submitCloudlets() {
//		int vmIndex = 0;
//		for (Cloudlet cloudlet : getCloudletList()) {
//			Vm vm;
//			// if user didn't bind this cloudlet and it has not been executed yet
//			if (cloudlet.getVmId() == -1) {
//				vm = getVmsCreatedList().get(vmIndex);
//			} else { // submit to the specific vm
//				vm = VmList.getById(getVmsCreatedList(), cloudlet.getVmId());
//				if (vm == null) { // vm was not created
//					Log.printLine(CloudSim.clock() + ": " + getName() + ": Postponing execution of cloudlet "
//							+ cloudlet.getCloudletId() + ": bount VM not available");
//					continue;
//				}
//			}
//			
//			double networkdelay=getNetworkDelay(getId(),vm.getId());
//			System.out.println("delay is "+networkdelay);
//
//			Log.printLine(CloudSim.clock() + ": " + getName() + ": Sending cloudlet "
//					+ cloudlet.getCloudletId() + " to VM #" + vm.getId());
//			bindCloudletToVm(cloudlet.getCloudletId(),vm.getId());
//			//cloudlet.setVmId(vm.getId());
//			sendNow(getVmsToDatacentersMap().get(vm.getId()), CloudSimTags.CLOUDLET_SUBMIT, cloudlet);
//			cloudletsSubmitted++;
//			vmIndex = (vmIndex + 1) % getVmsCreatedList().size();
//			getCloudletSubmittedList().add(cloudlet);
//		}
//
//		// remove submitted cloudlets from waiting list
//		for (Cloudlet cloudlet : getCloudletSubmittedList()) {
//			getCloudletList().remove(cloudlet);
//		}
//	}
	//fpa
	protected void submitCloudlets()
	{
	    double newsolfitness=0;
	    double fit=0;
	    //to store the final cloudlet assigning order
	    List<ArrayList<Integer>> cAssign=new ArrayList<ArrayList<Integer>>();
	    
		createPopulation();
		writeFile();
		
		//initialize fitness of each solution in initial population
	    for(int i=0;i<solutioncount;i++)
		{
			fitness[i][0]=0;
			fitness[i][1]=0;
		}
		
		//find fitness of each solution in initial population
		for(int i=0;i<solutioncount;i++)
		{
			fitness[i][0]=i;
			fitness[i][1]=checkFitness(Population.get(i));
		}
		
		System.out.println("\nFITNESS OF INITIAL SOLUTIONS-");
		//display fitness of initial population
		for(int i=0;i<solutioncount;i++)
		{
			System.out.println("Solution-"+i+" "+fitness[i][1]);
		}
		 
		//find best solution no
		int bestsolutionno=getBestSolutionNo(fitness);
		bestSoln.addAll(Population.get(bestsolutionno));
		 
		//display initial best solution
		System.out.println("\nINITIAL BEST SOLUTION-");
		System.out.println(bestSoln);
		 
		//run the iterations for 15 times
		for(int m=0;m<100;m++)
		{
		 //to generate new solutions
		 for(int i=0;i<solutioncount;i++)
		 {
			 //generate a random number between 0 to 1
			 double rand=Math.random();
		     if(rand<=0.8)
		     {
		    	 //get an another solution randomly from population
		    	 int othersol=new Random().nextInt(20);
		    	 //if both solutions are different
		    	 if(othersol!=i)
		    	 {
		    		 //call local pollination
		    		 newsol=localPollination(Population.get(i),Population.get(othersol));
		    		 
		         }
		    	 else if(othersol==i&&othersol!=0)
		    	 {
		    		 i--;
		    	 }
		    	 else if(othersol==i&&othersol==0)
		    	 {
		    		 othersol+=1;
		    		 //call local pollination
		    		 newsol=localPollination(Population.get(i),Population.get(othersol));
		    	 }
		     }
		     else
		     {
		    	 //call global pollination
		    	 newsol=globalPollination(Population.get(i),bestSoln);
		     }
		     
		     //check whether the newly generated solution is correct or not
		     checkNewSol();
		     
		     //find fitness of new solution
		     newsolfitness=checkFitness(newsol);
		     
		     //check whether the new solution is better than previous solution
		     if(newsolfitness<fitness[i][1])
		     {
		    	 Population.get(i).clear();
		    	 Population.get(i).addAll(newsol);
		    	 fitness[i][1]=newsolfitness;
		     }
		     //check whether the new solution is better than best solution
		     fit=checkFitness(bestSoln);
		     if(newsolfitness<fit)
		     {
		    	 bestsolutionno=i;
		    	 bestSoln.clear();
		    	 bestSoln.addAll(newsol);	 
		     }
		 }
		 fit=checkFitness(bestSoln);
		 if(m<99)
		  {
		     System.out.println("\nFitness of Best Solution in cycle "+m+" is-"+fit);
	         System.out.println(bestSoln);
		  }
		 else
		 {
			 System.out.println("\nFinal fitness is-"+fit);
	         System.out.println(bestSoln);
		 }
		}
		
		//initialize the list
		for(int i=0;i<getCloudletList().size();i++)
		{
			cAssign.add(new ArrayList<Integer>());
		}
		
	    //store vm numbers of cloudlets in list
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			for(int j=0;j<bestSoln.get(i).size();j++)
			{
				cAssign.get(bestSoln.get(i).get(j)).add(i);
			}
		}
		
		System.out.println("\nFINAL CLOUDLET ALLOCATIONS-");
		System.out.println(cAssign);
		
		int vmIndex = 0;
		for (Cloudlet cloudlet : getCloudletList()) {
			Vm vm;
			vm =getVmsCreatedList().get(cAssign.get(vmIndex).get(0));
			
			Log.printLine(CloudSim.clock() + ": " + getName() + ": Sending cloudlet "
					+ cloudlet.getCloudletId() + " to VM #" + vm.getId());
	        bindCloudletToVm(cloudlet.getCloudletId(),vm.getId());
			sendNow(getVmsToDatacentersMap().get(vm.getId()), CloudSimTags.CLOUDLET_SUBMIT, cloudlet);
			cloudletsSubmitted++;
			vmIndex = (vmIndex + 1);
			getCloudletSubmittedList().add(cloudlet);
		}

		// remove submitted cloudlets from waiting list
		for (Cloudlet cloudlet : getCloudletSubmittedList()) {
			getCloudletList().remove(cloudlet);
		}				
	}
	
	//create intial population
	protected void createPopulation()
	{
		this.avg=(getCloudletList().size()/getVmsCreatedList().size())+1;
		int []cloudletCount=new int[getVmsCreatedList().size()];
		
		//loop to generate initial solutions
		for(int i=0;i<solutioncount;i++)
		{
			//add a new row to the 3d list
			Population.add(new ArrayList<ArrayList<Integer>>());
			for(int j=0;j<getVmsCreatedList().size();j++)
			{
			    //add a new row to the 2d list.
				Population.get(i).add(new ArrayList<Integer>());
		    }
		}
			
			//to read from a file
			readFile();
			
//			//initialize the cloudletcount array to 0
//			Arrays.fill(cloudletCount,0);
//			for(int j=0;j<getCloudletList().size();j++)
//			{
//				int cloudletid=getCloudletList().get(j).getCloudletId();
//						
//				//randomly generating a vm from vmcreatedlist
//				int n=(int)(Math.random()*(getVmsCreatedList().size()));
//						
//				if(cloudletCount[n]<avg)
//				{
//				    //assigning cloudlet to selected vm
//				    Population.get(i).get(n).add(cloudletCount[n],cloudletid);
//				    cloudletCount[n]+=1;
//				}
//				else
//				{
//					j--;
//				}
//			  }
//		 }
		//display the initial poplulation
		System.out.println("\nINITIAL POPULATION-");
		for(int i=0;i<solutioncount;i++)
		{
			System.out.println("SOLUTION-"+i+" "+Population.get(i));
		}
	}
	
	//read population from the file
		protected void readFile() 
		{
			try 
			{	
				File myObj = new File("InitialPopulation.txt");
				Scanner myReader = new Scanner(myObj);
				int q = 0 ;int w =0;
				while (myReader.hasNextLine()) 
				{
					String data = myReader.nextLine();
					String[] dataSplit = data.trim().split(" ");
					if(dataSplit.length == 1)
					{
						if(dataSplit[0].equals("NEW")) {
							q++;
						    w = 0 ;
						}
						else if(dataSplit[0].equals(""))
						{
							w++;
						}
						else
						{
							Population.get(q).get(w).add(Integer.parseInt(dataSplit[0].trim()));
							w++;
						}
					}
					if(dataSplit.length != 1 ) {
					int[] dataSplitInt = new int[dataSplit.length];
					for (int i = 0; i < dataSplit.length; i++)
					{
						String var1 = dataSplit[i].trim();
						dataSplitInt[i] = Integer.parseInt(var1);
						Population.get(q).get(w).add(dataSplitInt[i]);
					}
					w++;
					}
				} 
				myReader.close();
			}
			catch (FileNotFoundException e) 
			{
				System.out.println("An error occurred.");
				e.printStackTrace();
			}
		}
	
	//write population to a file
		protected void writeFile() {
			try{    
			    FileWriter fw=new FileWriter("InitialPopulation.txt");    
			    int element = 0;
			    String str2;
			    for(int i=0;i <solutioncount;i++)
				{
			    	for(int j=0;j<Population.get(i).size();j++) 
			        {
						for(int k = 0; k<Population.get(i).get(j).size();k++) 
			        	{	
							element = Population.get(i).get(j).get(k);
						    str2 = Integer.toString(element); 
							fw.write(str2);
							fw.write(" ");
			        	}
						fw.write("\n");
			        }
			    	fw.write("NEW\n");
			   	}
		        fw.close();    
				}
				catch(Exception e){System.out.println(e);}
		}
	
	//fitness of any solution
	protected double checkFitness(ArrayList<ArrayList<Integer>> arr)
	{
		//exec time for each vm of a solution
	    double [] vmexectime=new double[getVmsCreatedList().size()];
	    
	    //total cloudletlength for a particular vm
	    long totalcloudletlength;
		
	    //initialize the vm execution time array to 0;
		Arrays.fill(vmexectime, 0);
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			//get a vm object to find its mips.
			Vm vm=getVmsCreatedList().get(i);
			double vmmips=vm.getMips();
			totalcloudletlength=0;
			for(int j=0;j<arr.get(i).size();j++)
			{
				//add all the cloudletlengths for a particular vm
				totalcloudletlength+=CloudletList.getById(getCloudletList(),arr.get(i).get(j)).getCloudletLength();
			}
				 
			//calculate time duration for each vm
			double duration=(double)totalcloudletlength/(double)vmmips;
			vmexectime[i]=duration;
		 }
		 
		 //find max of vmexectime and return it.
		 return maxExecTime(vmexectime);
	}
	
	//to find max time duration(makespan) for a solution.
	protected double maxExecTime(double[] arr)
	{
		double value=0;
		for(int i=0;i<arr.length;i++)
		{
			if(arr[i]>value)
			{
				value=arr[i];
			}
		}
		return value;
	}
	
	//to get best solution no
	protected int getBestSolutionNo(double arr[][])
	{
		int bestsolno=-1;
		double bestfitness=Integer.MAX_VALUE;
		for(int i=0;i<solutioncount;i++) 
		{
			if(arr[i][1]<bestfitness)
			{
				bestfitness=arr[i][1];
				bestsolno=i;
			}
		}
		return bestsolno;
	}
	
	//to generate new solution by local pollination
	
	protected ArrayList localPollination(ArrayList<ArrayList<Integer>> sol1,ArrayList<ArrayList<Integer>> sol2)
	{
		//initialize a 2d arraylist to store new solution
		ArrayList<ArrayList<Integer>> newsol=new ArrayList<ArrayList<Integer>>();
		
		for(int i=0;i<getVmsCreatedList().size();i++)
		 {
			newsol.add(new ArrayList<Integer>());
		 }
		
		//generate a random number between 0 to 11
		int random=new Random().nextInt(getVmsCreatedList().size());
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			if(i<=random)
			{
				//copy from 1st sol to new sol
				newsol.get(i).addAll(sol1.get(i));
			}
			
			else
			{
				//copy from 2nd sol to new sol
				newsol.get(i).addAll(sol2.get(i));
			}
		}	
		return newsol;
	}
	
	//to generate new solution by global pollination
	
	protected ArrayList globalPollination(ArrayList<ArrayList<Integer>> sol1,ArrayList<ArrayList<Integer>> sol2)
	{
		//initialize a 2d arraylist to store new solution
        ArrayList<ArrayList<Integer>> newsol=new ArrayList<ArrayList<Integer>>();
		
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			newsol.add(new ArrayList<Integer>());
		}
		
		//generate a random number between 0 to 11
		int random=new Random().nextInt(getVmsCreatedList().size());
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			//copy from 1st sol to newsol
			if(i<=random)
			{
				newsol.get(i).addAll(sol1.get(i));
			}
			
			else
			{
				//copy from 2nd sol to new sol
				newsol.get(i).addAll(sol2.get(i));
			}
		}
		return newsol;	
	}
	
	//to check the correctness of the new solution
	protected void checkNewSol()
	{
		this.vmTimes=new double[getVmsCreatedList().size()][2];
		//to store the vms on which cloudlets are assigned
		List<ArrayList<Integer>> cloudletAssign=new ArrayList<ArrayList<Integer>>();
		
		//initialize the list
		for(int i=0;i<getCloudletList().size();i++)
		{
			cloudletAssign.add(new ArrayList<Integer>());
		}
		
		
		//store vm numbers of cloudlets in list
		for(int i=0;i<getVmsCreatedList().size();i++)
		{
			for(int j=0;j<newsol.get(i).size();j++)
			{
				cloudletAssign.get(newsol.get(i).get(j)).add(i);
			}
		}
		
		//check the count of vms on which clouldlet is assigned and correct the solution
		for(int i=0;i<getCloudletList().size();i++)
		{
			if(cloudletAssign.get(i).size()>1)
			{
				deleteMultipleAssignedCloudlet(i,cloudletAssign.get(i));
			}
		}
		
		//check the count of vms on which clouldlet is assigned and correct the solution
		for(int i=0;i<getCloudletList().size();i++)
		{
			if(cloudletAssign.get(i).size()==0)
			{
				AssignUnassignedCloudlet(i);
			}
		}
	
	}

	//to assign unassigned cloudlets
    protected void AssignUnassignedCloudlet(int i)
    {
    	getVmExecutionTimes();
    	vmTimesSort(vmTimes);
    	
    	//assign the cloudlet to the vm which has least execution time and is not overflowed
    	for(int j=0;j<getVmsCreatedList().size();j++)
    	{
    		if(newsol.get((int) vmTimes[j][0]).size()<avg)
    		{
    			newsol.get((int)vmTimes[j][0]).add(i);
    			break;
    		}
    	}
    }
    
    //to delete multiple assigned cloudlets
    protected void deleteMultipleAssignedCloudlet(int i,List<Integer> ls)
    {
    	getVmExecutionTimes();
    	 	
    	//if 1st vm has more exec time than 2nd,remove from 1st one
    	if((vmTimes[ls.get(0)][1]>=vmTimes[ls.get(1)][1]))
    	{
    		for(int j=0;j<newsol.get(ls.get(0)).size();j++)
    		{
    			if(newsol.get(ls.get(0)).get(j)==i)
    			{
    				newsol.get(ls.get(0)).remove(j);
    			}
    		}
    	}
    	//if 2nd vm has more exec time,remove from 2nd one
    	else if((vmTimes[ls.get(0)][1]<=vmTimes[ls.get(1)][1]))
    	{
    		for(int j=0;j<newsol.get(ls.get(1)).size();j++)
    		{
    			if(newsol.get(ls.get(1)).get(j)==i)
    			{
    				newsol.get(ls.get(1)).remove(j);
    			}
    		}
    	}
    }
    
    //to get vm execution time for each vm of new solution
    protected void getVmExecutionTimes()
    {
    	//total cloudletlength for a particular vm
	    long totalcloudletlength;
    	
    	for(int i=0;i<getVmsCreatedList().size();i++)
		{
			//get a vm object to find its mips.
			Vm vm=getVmsCreatedList().get(i);
			double vmmips=vm.getMips();
			totalcloudletlength=0;
			for(int j=0;j<newsol.get(i).size();j++)
			{
				//add all the cloudletlengths for a particular vm
				totalcloudletlength+=CloudletList.getById(getCloudletList(),newsol.get(i).get(j)).getCloudletLength();
			}
			double duration=(double)totalcloudletlength/(double)vmmips;
			vmTimes[i][0]=i;
			vmTimes[i][1]=duration;	
		}	
    }

	
	//to sort the vmexec times of vms of a new solution
	protected void vmTimesSort(double[][] arr)
	{
		int rows=arr.length;
		
		double temp,temp1;
	    int k=0,i=0;
	    for(k=0;k<rows-1;k++)
		 {
	        for(i=0;i<rows-k-1;i++) 
			{
	            if(arr[i][1]>arr[i+1][1] )
				{
	                temp=arr[i][1];
	                arr[i][1]=arr[i+1][1];
	                arr[i+1][1]=temp;
	                
	                temp1=arr[i][0];
	                arr[i][0] = arr[i+1][0];
	                arr[i+1][0]=temp1;
	            }
	        }
	    }
	}
	
	/**
	 * Destroy the virtual machines running in datacenters.
	 * 
	 * @pre $none
	 * @post $none
	 */
	protected void clearDatacenters() {
		for (Vm vm : getVmsCreatedList()) {
			Log.printLine(CloudSim.clock() + ": " + getName() + ": Destroying VM #" + vm.getId());
			sendNow(getVmsToDatacentersMap().get(vm.getId()), CloudSimTags.VM_DESTROY, vm);
		}

		getVmsCreatedList().clear();
	}

	/**
	 * Send an internal event communicating the end of the simulation.
	 * 
	 * @pre $none
	 * @post $none
	 */
	protected void finishExecution() {
		sendNow(getId(), CloudSimTags.END_OF_SIMULATION);
	}

	/*
	 * (non-Javadoc)
	 * @see cloudsim.core.SimEntity#shutdownEntity()
	 */
	@Override
	public void shutdownEntity() {
		Log.printLine(getName() + " is shutting down...");
	}

	/*
	 * (non-Javadoc)
	 * @see cloudsim.core.SimEntity#startEntity()
	 */
	@Override
	public void startEntity() {
		Log.printLine(getName() + " is starting...");
		schedule(getId(), 0, CloudSimTags.RESOURCE_CHARACTERISTICS_REQUEST);
	}

	/**
	 * Gets the vm list.
	 * 
	 * @param <T> the generic type
	 * @return the vm list
	 */
	@SuppressWarnings("unchecked")
	public <T extends Vm> List<T> getVmList() {
		return (List<T>) vmList;
	}

	/**
	 * Sets the vm list.
	 * 
	 * @param <T> the generic type
	 * @param vmList the new vm list
	 */
	protected <T extends Vm> void setVmList(List<T> vmList) {
		this.vmList = vmList;
	}

	/**
	 * Gets the cloudlet list.
	 * 
	 * @param <T> the generic type
	 * @return the cloudlet list
	 */
	@SuppressWarnings("unchecked")
	public <T extends Cloudlet> List<T> getCloudletList() {
		return (List<T>) cloudletList;
	}

	/**
	 * Sets the cloudlet list.
	 * 
	 * @param <T> the generic type
	 * @param cloudletList the new cloudlet list
	 */
	protected <T extends Cloudlet> void setCloudletList(List<T> cloudletList) {
		this.cloudletList = cloudletList;
	}

	/**
	 * Gets the cloudlet submitted list.
	 * 
	 * @param <T> the generic type
	 * @return the cloudlet submitted list
	 */
	@SuppressWarnings("unchecked")
	public <T extends Cloudlet> List<T> getCloudletSubmittedList() {
		return (List<T>) cloudletSubmittedList;
	}

	/**
	 * Sets the cloudlet submitted list.
	 * 
	 * @param <T> the generic type
	 * @param cloudletSubmittedList the new cloudlet submitted list
	 */
	protected <T extends Cloudlet> void setCloudletSubmittedList(List<T> cloudletSubmittedList) {
		this.cloudletSubmittedList = cloudletSubmittedList;
	}

	/**
	 * Gets the cloudlet received list.
	 * 
	 * @param <T> the generic type
	 * @return the cloudlet received list
	 */
	@SuppressWarnings("unchecked")
	public <T extends Cloudlet> List<T> getCloudletReceivedList() {
		return (List<T>) cloudletReceivedList;
	}

	/**
	 * Sets the cloudlet received list.
	 * 
	 * @param <T> the generic type
	 * @param cloudletReceivedList the new cloudlet received list
	 */
	protected <T extends Cloudlet> void setCloudletReceivedList(List<T> cloudletReceivedList) {
		this.cloudletReceivedList = cloudletReceivedList;
	}

	/**
	 * Gets the vm list.
	 * 
	 * @param <T> the generic type
	 * @return the vm list
	 */
	@SuppressWarnings("unchecked")
	public <T extends Vm> List<T> getVmsCreatedList() {
		return (List<T>) vmsCreatedList;
	}

	/**
	 * Sets the vm list.
	 * 
	 * @param <T> the generic type
	 * @param vmsCreatedList the vms created list
	 */
	protected <T extends Vm> void setVmsCreatedList(List<T> vmsCreatedList) {
		this.vmsCreatedList = vmsCreatedList;
	}

	/**
	 * Gets the vms requested.
	 * 
	 * @return the vms requested
	 */
	protected int getVmsRequested() {
		return vmsRequested;
	}

	/**
	 * Sets the vms requested.
	 * 
	 * @param vmsRequested the new vms requested
	 */
	protected void setVmsRequested(int vmsRequested) {
		this.vmsRequested = vmsRequested;
	}

	/**
	 * Gets the vms acks.
	 * 
	 * @return the vms acks
	 */
	protected int getVmsAcks() {
		return vmsAcks;
	}

	/**
	 * Sets the vms acks.
	 * 
	 * @param vmsAcks the new vms acks
	 */
	protected void setVmsAcks(int vmsAcks) {
		this.vmsAcks = vmsAcks;
	}

	/**
	 * Increment vms acks.
	 */
	protected void incrementVmsAcks() {
		vmsAcks++;
	}

	/**
	 * Gets the vms destroyed.
	 * 
	 * @return the vms destroyed
	 */
	protected int getVmsDestroyed() {
		return vmsDestroyed;
	}

	/**
	 * Sets the vms destroyed.
	 * 
	 * @param vmsDestroyed the new vms destroyed
	 */
	protected void setVmsDestroyed(int vmsDestroyed) {
		this.vmsDestroyed = vmsDestroyed;
	}

	/**
	 * Gets the datacenter ids list.
	 * 
	 * @return the datacenter ids list
	 */
	protected List<Integer> getDatacenterIdsList() {
		return datacenterIdsList;
	}

	/**
	 * Sets the datacenter ids list.
	 * 
	 * @param datacenterIdsList the new datacenter ids list
	 */
	protected void setDatacenterIdsList(List<Integer> datacenterIdsList) {
		this.datacenterIdsList = datacenterIdsList;
	}

	/**
	 * Gets the vms to datacenters map.
	 * 
	 * @return the vms to datacenters map
	 */
	protected Map<Integer, Integer> getVmsToDatacentersMap() {
		return vmsToDatacentersMap;
	}

	/**
	 * Sets the vms to datacenters map.
	 * 
	 * @param vmsToDatacentersMap the vms to datacenters map
	 */
	protected void setVmsToDatacentersMap(Map<Integer, Integer> vmsToDatacentersMap) {
		this.vmsToDatacentersMap = vmsToDatacentersMap;
	}

	/**
	 * Gets the datacenter characteristics list.
	 * 
	 * @return the datacenter characteristics list
	 */
	protected Map<Integer, DatacenterCharacteristics> getDatacenterCharacteristicsList() {
		return datacenterCharacteristicsList;
	}

	/**
	 * Sets the datacenter characteristics list.
	 * 
	 * @param datacenterCharacteristicsList the datacenter characteristics list
	 */
	protected void setDatacenterCharacteristicsList(
			Map<Integer, DatacenterCharacteristics> datacenterCharacteristicsList) {
		this.datacenterCharacteristicsList = datacenterCharacteristicsList;
	}

	/**
	 * Gets the datacenter requested ids list.
	 * 
	 * @return the datacenter requested ids list
	 */
	protected List<Integer> getDatacenterRequestedIdsList() {
		return datacenterRequestedIdsList;
	}

	/**
	 * Sets the datacenter requested ids list.
	 * 
	 * @param datacenterRequestedIdsList the new datacenter requested ids list
	 */
	protected void setDatacenterRequestedIdsList(List<Integer> datacenterRequestedIdsList) {
		this.datacenterRequestedIdsList = datacenterRequestedIdsList;
	}

}
