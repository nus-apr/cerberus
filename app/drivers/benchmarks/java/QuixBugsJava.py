import os
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core import abstractions
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class QuixBugsJava(AbstractBenchmark):
    """
    Template for the Maven project created for each instance.
    """

    __MAVEN_TEMPLATE = """<?xml version="1.0" encoding="UTF-8"?>
    <project xmlns="http://maven.apache.org/POM/4.0.0" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
    xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
 <modelVersion>4.0.0</modelVersion> <groupId>org.example</groupId>
 <artifactId>quixbugs-bug</artifactId>
 <version>1.0-SNAPSHOT</version> <name>quixbugs-bug</name> <url>http://www.example.com</url> <properties>
   <project.build.sourceEncoding>UTF-8</project.build.sourceEncoding>
   <maven.compiler.source>1.7</maven.compiler.source>
   <maven.compiler.target>1.7</maven.compiler.target>
 </properties> <dependencies>
   <dependency>
     <groupId>junit</groupId>
     <artifactId>junit</artifactId>
     <version>4.12</version>
     <scope>test</scope>
   </dependency>
   <dependency>
     <groupId>org.xmlunit</groupId>
     <artifactId>xmlunit-core</artifactId>
     <version>2.8.2</version>
   </dependency>
   <!-- https://mvnrepository.com/artifact/org.xmlunit/xmlunit-matchers -->
   <dependency>
     <groupId>org.xmlunit</groupId>
     <artifactId>xmlunit-matchers</artifactId>
     <version>2.8.2</version>
   </dependency> </dependencies> <build>
   <pluginManagement><!-- lock down plugins versions to avoid using Maven defaults (may be moved to parent pom) -->
     <plugins>
       <!-- clean lifecycle, see https://maven.apache.org/ref/current/maven-core/lifecycles.html#clean_Lifecycle -->
       <plugin>
         <artifactId>maven-clean-plugin</artifactId>
         <version>3.1.0</version>
       </plugin>
       <!-- default lifecycle, jar packaging: see https://maven.apache.org/ref/current/maven-core/default-bindings.html#Plugin_bindings_for_jar_packaging -->
       <plugin>
         <artifactId>maven-resources-plugin</artifactId>
         <version>3.0.2</version>
       </plugin>
       <plugin>
         <artifactId>maven-compiler-plugin</artifactId>
         <version>3.8.0</version>
       </plugin>
       <plugin>
         <artifactId>maven-jar-plugin</artifactId>
         <version>3.0.2</version>
       </plugin>
       <plugin>
         <artifactId>maven-install-plugin</artifactId>
         <version>2.5.2</version>
       </plugin>
       <plugin>
         <artifactId>maven-deploy-plugin</artifactId>
         <version>2.8.2</version>
       </plugin>
       <!-- site lifecycle, see https://maven.apache.org/ref/current/maven-core/lifecycles.html#site_Lifecycle -->
       <plugin>
         <artifactId>maven-site-plugin</artifactId>
         <version>3.7.1</version>
       </plugin>
       <plugin>
         <artifactId>maven-project-info-reports-plugin</artifactId>
         <version>3.0.0</version>
       </plugin>
     </plugins>
   </pluginManagement>
   <plugins>
     <plugin>
       <groupId>org.apache.maven.plugins</groupId>
       <artifactId>maven-compiler-plugin</artifactId>
       <configuration>
         <source>8</source>
         <target>8</target>
       </configuration>
     </plugin>
     <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-surefire-plugin</artifactId>
        <version>3.0.0-M7</version>
        <configuration>
            <includes>
                <include>**/*_UT.java</include>
                <include>**/*_TEST.java</include>
            </includes>
        </configuration>
     </plugin>
   </plugins>
 </build>
</project>
    """

    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(QuixBugsJava, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(QuixBugsJava, self).setup_experiment(
            bug_index, container_id, test_all
        )
        if not is_error:
            if self.instrument(bug_index, container_id):
                self.emit_success("[benchmark] instrumentation successful")
            else:
                self.emit_error("[benchmark] instrumentation failed")
                is_error = True
        return is_error

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(QuixBugsJava, self).setup_container(
            bug_index, image_name, cpu, gpu
        )

        root = join(self.dir_expr, "src")

        self.run_command(
            container_id,
            "mkdir -p {}".format(join(root, "src", "main", "java", "java_programs")),
        )

        self.run_command(
            container_id,
            "mkdir -p {}".format(join(root, "src", "test", "java", "java_testcases")),
        )

        abstractions.write_file(
            container_id, [QuixBugsJava.__MAVEN_TEMPLATE], join(root, "pom.xml")
        )

        self.run_command(
            container_id,
            "cp -r {}/java_programs {}".format(
                self.dir_setup, join(root, "src", "main", "java")
            ),
        )
        self.run_command(
            container_id,
            "cp -r {}/java_testcases {}".format(
                self.dir_setup, join(root, "src", "test", "java")
            ),
        )
        return container_id

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        return True

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        status = self.run_command(
            container_id, "mvn compile", dir_path=join(self.dir_expr, "src")
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        status = self.run_command(
            container_id, "mvn test", dir_path=join(self.dir_expr, "src")
        )
        return status != 0

    def instrument(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("instrumenting assertions")
        return True

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(QuixBugsJava, self).save_artifacts(dir_info, container_id)
