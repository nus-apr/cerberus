# Add New Tool
In order to add a new analyze/repair tool to the framework, the following requirements should be met

* Tool Driver: python class that extends AbstractTool to facilitate standardization of interfaces
* Tool image (optional): to enable container virtualization, a Dockerfile is required or the tool should be invokable from the CLI


## Adding a Driver
Create a new file in `app/drivers/tools/[analyze/repair]` with the Tool name (i.e. NewTool.py).
Depending on the tool you may follow the instructions

* [Analysis Tool](AnalyzeTool.md)
* [Repair Tool](RepairTool.md)

